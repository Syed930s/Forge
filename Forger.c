// Write the full Forger.c with all fixes + SC syscall support
/* ok
 * FORGER - The Forge Language Compiler
 * Single-file. Build: gcc -O2 -o forger Forger.c
 * Targets: ELF64, PE32+, Mach-O 64, flat, custom (.fgl)
 * Arch:    x86-64 (System V ABI / Linux syscalls)
 *
 * NEW: SC(num, a, b, c, d, e, f) — native syscall from Forge source
 *      e.g.  SC(1, 1, buf_ptr, len, 0, 0, 0)  = write(1, buf, len)
 *            SC(60, 0, 0, 0, 0, 0, 0)          = exit(0)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>

/* ---------- SECTION 1: PLATFORM + TYPES ---------- */
#if defined(_WIN32)||defined(_WIN64)
#define PLATFORM_WINDOWS 1
#else
#define PLATFORM_WINDOWS 0
#endif
typedef unsigned char      u8;
typedef unsigned short     u16;
typedef unsigned int       u32;
typedef unsigned long long u64;
typedef signed char        i8;
typedef signed short       i16;
typedef signed int         i32;
typedef signed long long   i64;
typedef u8                 bool8;
#define TRUE  1
#define FALSE 0

/* ---------- SECTION 2: ARENA ---------- */
#define ARENA_BLOCK (1<<20)
typedef struct ArenaBlock { u8 *data; u32 used,cap; struct ArenaBlock *next; } ArenaBlock;
typedef struct { ArenaBlock *head,*cur; } Arena;
static ArenaBlock *anew(u32 min) {
    ArenaBlock *b=malloc(sizeof*b);
    u32 c=min>ARENA_BLOCK?min:ARENA_BLOCK;
    b->data=malloc(c);b->used=0;b->cap=c;b->next=0;return b;
}
static void arena_init(Arena *a){a->head=anew(ARENA_BLOCK);a->cur=a->head;}
static void *arena_alloc(Arena *a,u32 sz){
    void *p;u32 al=(sz+7)&~7u;if(!al)al=8;
    if(a->cur->used+al>a->cur->cap){ArenaBlock *b=anew(al);a->cur->next=b;a->cur=b;}
    p=a->cur->data+a->cur->used;a->cur->used+=al;memset(p,0,al);return p;
}
static char *astrdup(Arena *a,const char *s){
    u32 n=(u32)strlen(s)+1;char *o=arena_alloc(a,n);memcpy(o,s,n);return o;
}
static void arena_free(Arena *a){
    ArenaBlock *b=a->head;
    while(b){ArenaBlock *nx=b->next;free(b->data);free(b);b=nx;}
    a->head=a->cur=0;
}

/* ---------- SECTION 3: ERRORS ---------- */
static const char *g_src="";
static int g_errs=0,g_verbose=0;
typedef enum{SEV_W,SEV_E,SEV_F}Sev;
static void report(Sev s,int l,int c,const char*fmt,...){
    va_list ap;const char*p=s==SEV_W?"warning":s==SEV_E?"error":"fatal";
    fprintf(stderr,"%s:%d:%d: %s: ",g_src,l,c,p);
    va_start(ap,fmt);vfprintf(stderr,fmt,ap);va_end(ap);fputs("\n",stderr);
    if(s==SEV_E)g_errs++;
    if(s==SEV_F){fputs("forger: aborted\n",stderr);exit(1);}
}
#define WARN(l,c,...) report(SEV_W,l,c,__VA_ARGS__)
#define ERR(l,c,...)  report(SEV_E,l,c,__VA_ARGS__)
#define FATAL(l,c,...) report(SEV_F,l,c,__VA_ARGS__)

/* ---------- SECTION 4: TYPES ---------- */
typedef enum{
    TY_VOID,TY_BOOL,TY_I8,TY_I16,TY_I32,TY_I64,
    TY_U8,TY_U16,TY_U32,TY_U64,TY_F32,TY_F64,TY_CHAR,
    TY_PTR,TY_ARRAY,TY_STRUCT,TY_FN,TY_UNK
}TypeKind;
typedef struct Type Type;
typedef struct TF{char*name;Type*type;struct TF*next;}TF; /* TypeField */
struct Type{TypeKind k;Type*base;u32 arr_sz;char*name;TF*fields;
    Type**ptypes;int pcount;Type*ret;};
static Arena g_ty_arena;
static Type*tnew(TypeKind k){Type*t=arena_alloc(&g_ty_arena,sizeof*t);t->k=k;return t;}
static Type *TV,*TB,*TI8,*TI16,*TI32,*TI64,*TU8,*TU16,*TU32,*TU64,
            *TF32,*TF64,*TCH,*TUN;
static void types_init(void){
    arena_init(&g_ty_arena);
    TV=tnew(TY_VOID);TB=tnew(TY_BOOL);
    TI8=tnew(TY_I8);TI16=tnew(TY_I16);TI32=tnew(TY_I32);TI64=tnew(TY_I64);
    TU8=tnew(TY_U8);TU16=tnew(TY_U16);TU32=tnew(TY_U32);TU64=tnew(TY_U64);
    TF32=tnew(TY_F32);TF64=tnew(TY_F64);TCH=tnew(TY_CHAR);TUN=tnew(TY_UNK);
}
static Type*tptr(Type*b){Type*t=tnew(TY_PTR);t->base=b;return t;}
static u32 tsz(Type*t){
    if(!t)return 0;
    switch(t->k){
        case TY_VOID:return 0;
        case TY_BOOL:case TY_I8:case TY_U8:case TY_CHAR:return 1;
        case TY_I16:case TY_U16:return 2;
        case TY_I32:case TY_U32:case TY_F32:return 4;
        case TY_I64:case TY_U64:case TY_F64:case TY_PTR:return 8;
        case TY_ARRAY:return t->arr_sz*tsz(t->base);
        case TY_STRUCT:{TF*f=t->fields;u32 s=0;while(f){s+=tsz(f->type);f=f->next;}return s;}
        default:return 0;
    }
}
static bool8 tis_int(Type*t){return t&&((t->k>=TY_I8&&t->k<=TY_U64)||t->k==TY_CHAR||t->k==TY_BOOL);}
static bool8 tis_flt(Type*t){return t&&(t->k==TY_F32||t->k==TY_F64);}
static bool8 teq(Type*a,Type*b){
    if(a==b)return TRUE;if(!a||!b)return FALSE;
    if(a->k==TY_UNK||b->k==TY_UNK)return TRUE;
    if(tis_int(a)&&tis_int(b))return TRUE;
    if(tis_flt(a)&&tis_flt(b))return TRUE;
    if(a->k!=b->k)return FALSE;
    if(a->k==TY_PTR){
        if(!a->base||!b->base)return TRUE;
        if(a->base->k==TY_VOID||b->base->k==TY_VOID)return TRUE;
        return teq(a->base,b->base);
    }
    if(a->k==TY_STRUCT)return a->name&&b->name&&!strcmp(a->name,b->name);
    return FALSE;
}
static const char*tname(Type*t){
    if(!t)return"?";
    switch(t->k){
        case TY_VOID:return"vd";case TY_BOOL:return"bl";
        case TY_I8:return"i8";case TY_I16:return"i16";case TY_I32:return"i32";case TY_I64:return"i64";
        case TY_U8:return"u8";case TY_U16:return"u16";case TY_U32:return"u32";case TY_U64:return"u64";
        case TY_F32:return"f32";case TY_F64:return"f64";case TY_CHAR:return"ch";case TY_PTR:return"pt";
        case TY_STRUCT:return t->name?t->name:"struct";default:return"?";
    }
}

/* ---------- SECTION 5: LEXER ---------- */
typedef enum{
    TK_INT,TK_FLT,TK_CHR,TK_STR,TK_ID,
    /* keywords */
    TK_V,TK_PV,TK_PS,TK_P,TK_FN,TK_RT,TK_IF,TK_EL,TK_ELF,
    TK_LP,TK_FR,TK_BK,TK_SK,TK_PT_KW,TK_DR,TK_ST,TK_AL,TK_FF,
    TK_IM,TK_ASM,TK_EX,TK_CB,TK_SZ,TK_CT,TK_NL,TK_TR,TK_FL_K,
    TK_SC,  /* SC(num,a,b,c,d,e,f) — native syscall */
    /* type keywords */
    TK_TVD,TK_TBL,TK_TI8,TK_TI16,TK_TI32,TK_TI64,
    TK_TU8,TK_TU16,TK_TU32,TK_TU64,TK_TF32,TK_TF64,TK_TCH,TK_TSTR,TK_TPT,
    /* operators */
    TK_PLUS,TK_MINUS,TK_STAR,TK_SLASH,TK_PCT,
    TK_AMP,TK_PIPE,TK_CARET,TK_TILDE,TK_BANG,
    TK_SHL,TK_SHR,
    TK_EQ,TK_NEQ,TK_LT,TK_GT,TK_LTE,TK_GTE,
    TK_AND,TK_OR,
    TK_ASGN,TK_PASGN,TK_MASGN,TK_SASGN,TK_DASGN,
    TK_INC,TK_DEC,TK_ARR,TK_DOT,
    TK_LP2,TK_RP,TK_LB,TK_RB,TK_LBK,TK_RBK,
    TK_SEMI,TK_COL,TK_COM,TK_HASH,
    TK_EOF,TK_UNK
}TK;
typedef struct{TK k;int ln,cl;char*sv;i64 iv;double fv;}Token;
typedef struct{const char*src;u32 pos,len;int ln,cl;Arena*arena;Token*toks;u32 ntok,tcap;}Lexer;

static struct{const char*kw;TK tk;}g_kw[]={
    {"V",TK_V},{"PV",TK_PV},{"PS",TK_PS},{"P",TK_P},{"FN",TK_FN},
    {"RT",TK_RT},{"IF",TK_IF},{"EL",TK_EL},{"ELF",TK_ELF},{"LP",TK_LP},
    {"FR",TK_FR},{"BK",TK_BK},{"SK",TK_SK},{"PT",TK_PT_KW},{"DR",TK_DR},
    {"ST",TK_ST},{"AL",TK_AL},{"FF",TK_FF},{"IM",TK_IM},{"ASM",TK_ASM},
    {"EX",TK_EX},{"CB",TK_CB},{"SZ",TK_SZ},{"CT",TK_CT},{"NL",TK_NL},
    {"TR",TK_TR},{"FL",TK_FL_K},{"SC",TK_SC},
    {"vd",TK_TVD},{"bl",TK_TBL},
    {"i8",TK_TI8},{"i16",TK_TI16},{"i32",TK_TI32},{"i64",TK_TI64},
    {"u8",TK_TU8},{"u16",TK_TU16},{"u32",TK_TU32},{"u64",TK_TU64},
    {"f32",TK_TF32},{"f64",TK_TF64},{"ch",TK_TCH},{"str",TK_TSTR},{"pt",TK_TPT},
    {0,TK_UNK}
};
static TK kw_lookup(const char*s){int i;for(i=0;g_kw[i].kw;i++)if(!strcmp(g_kw[i].kw,s))return g_kw[i].tk;return TK_ID;}
static void lpush(Lexer*l,Token t){
    if(l->ntok>=l->tcap){l->tcap=l->tcap?l->tcap*2:256;l->toks=realloc(l->toks,sizeof(Token)*l->tcap);}
    l->toks[l->ntok++]=t;
}
static char lp(Lexer*l){return l->pos<l->len?l->src[l->pos]:0;}
static char lp2(Lexer*l){return l->pos+1<l->len?l->src[l->pos+1]:0;}
static char la(Lexer*l){char c=l->src[l->pos++];if(c=='\n'){l->ln++;l->cl=1;}else l->cl++;return c;}
static void lexer_lex(Lexer*l){
    while(l->pos<l->len){
        char c;int ln,cl;
        while(l->pos<l->len&&(l->src[l->pos]==' '||l->src[l->pos]=='\t'||l->src[l->pos]=='\r'||l->src[l->pos]=='\n'))la(l);
        if(l->pos>=l->len)break;
        c=l->src[l->pos];ln=l->ln;cl=l->cl;
        /* line comment */
        if(c=='/'&&lp2(l)=='/'){while(l->pos<l->len&&l->src[l->pos]!='\n')l->pos++;continue;}
        /* block comment */
        if(c=='/'&&lp2(l)=='*'){l->pos+=2;l->cl+=2;
            while(l->pos+1<l->len&&!(l->src[l->pos]=='*'&&l->src[l->pos+1]=='/'))la(l);
            if(l->pos+1<l->len){l->pos+=2;l->cl+=2;}continue;}
        /* string */
        if(c=='"'){
            char buf[8192];u32 bi=0;Token t;
            t.ln=ln;t.cl=cl;t.k=TK_STR;t.iv=0;t.fv=0;
            la(l);
            while(l->pos<l->len&&l->src[l->pos]!='"'){
                char ch=la(l);
                if(ch=='\\'){char e=la(l);switch(e){case 'n':buf[bi++]='\n';break;case 't':buf[bi++]='\t';break;
                    case 'r':buf[bi++]='\r';break;case '0':buf[bi++]=0;break;
                    case '\\':buf[bi++]='\\';break;case '"':buf[bi++]='"';break;default:buf[bi++]=e;break;}}
                else buf[bi++]=ch;
                if(bi>=sizeof(buf)-1)break;
            }
            if(l->pos<l->len)la(l);
            buf[bi]=0;t.sv=astrdup(l->arena,buf);lpush(l,t);continue;
        }
        /* char */
        if(c=='\''){
            Token t;t.ln=ln;t.cl=cl;t.k=TK_CHR;t.sv=0;t.fv=0;
            la(l);
            if(l->pos<l->len&&l->src[l->pos]=='\\'){char e;la(l);e=la(l);
                switch(e){case 'n':t.iv='\n';break;case 't':t.iv='\t';break;case '0':t.iv=0;break;default:t.iv=e;break;}}
            else t.iv=(l->pos<l->len)?la(l):0;
            if(l->pos<l->len&&l->src[l->pos]=='\'')la(l);
            lpush(l,t);continue;
        }
        /* number */
        if(c>='0'&&c<='9'){
            char buf[64];u32 bi=0;Token t;bool8 flt=0,hex=0;
            t.ln=ln;t.cl=cl;t.sv=0;
            if(c=='0'&&(lp2(l)=='x'||lp2(l)=='X')){buf[bi++]=la(l);buf[bi++]=la(l);hex=1;
                while(l->pos<l->len&&((l->src[l->pos]>='0'&&l->src[l->pos]<='9')||(l->src[l->pos]>='a'&&l->src[l->pos]<='f')||(l->src[l->pos]>='A'&&l->src[l->pos]<='F')))buf[bi++]=la(l);}
            else{while(l->pos<l->len&&l->src[l->pos]>='0'&&l->src[l->pos]<='9')buf[bi++]=la(l);
                if(l->pos<l->len&&l->src[l->pos]=='.'){flt=1;buf[bi++]=la(l);
                    while(l->pos<l->len&&l->src[l->pos]>='0'&&l->src[l->pos]<='9')buf[bi++]=la(l);}}
            buf[bi]=0;
            if(flt){t.k=TK_FLT;t.fv=atof(buf);t.iv=0;}
            else{t.k=TK_INT;t.iv=(i64)strtoll(buf,0,hex?16:10);t.fv=0;}
            lpush(l,t);continue;
        }
        /* ident/keyword */
        if((c>='a'&&c<='z')||(c>='A'&&c<='Z')||c=='_'){
            char buf[256];u32 bi=0;Token t;t.ln=ln;t.cl=cl;t.iv=0;t.fv=0;
            while(l->pos<l->len&&((l->src[l->pos]>='a'&&l->src[l->pos]<='z')||(l->src[l->pos]>='A'&&l->src[l->pos]<='Z')||(l->src[l->pos]>='0'&&l->src[l->pos]<='9')||l->src[l->pos]=='_'))buf[bi++]=la(l);
            buf[bi]=0;t.k=kw_lookup(buf);t.sv=astrdup(l->arena,buf);lpush(l,t);continue;
        }
        /* operators */
        {Token t;t.ln=ln;t.cl=cl;t.sv=0;t.iv=0;t.fv=0;la(l);
         switch(c){
             case '+':if(lp(l)=='+'){la(l);t.k=TK_INC;}else if(lp(l)=='='){la(l);t.k=TK_PASGN;}else t.k=TK_PLUS;break;
             case '-':if(lp(l)=='-'){la(l);t.k=TK_DEC;}else if(lp(l)=='='){la(l);t.k=TK_MASGN;}else if(lp(l)=='>'){la(l);t.k=TK_ARR;}else t.k=TK_MINUS;break;
             case '*':if(lp(l)=='='){la(l);t.k=TK_SASGN;}else t.k=TK_STAR;break;
             case '/':if(lp(l)=='='){la(l);t.k=TK_DASGN;}else t.k=TK_SLASH;break;
             case '%':t.k=TK_PCT;break;
             case '&':if(lp(l)=='&'){la(l);t.k=TK_AND;}else t.k=TK_AMP;break;
             case '|':if(lp(l)=='|'){la(l);t.k=TK_OR;}else t.k=TK_PIPE;break;
             case '^':t.k=TK_CARET;break;case '~':t.k=TK_TILDE;break;
             case '!':if(lp(l)=='='){la(l);t.k=TK_NEQ;}else t.k=TK_BANG;break;
             case '<':if(lp(l)=='<'){la(l);t.k=TK_SHL;}else if(lp(l)=='='){la(l);t.k=TK_LTE;}else t.k=TK_LT;break;
             case '>':if(lp(l)=='>'){la(l);t.k=TK_SHR;}else if(lp(l)=='='){la(l);t.k=TK_GTE;}else t.k=TK_GT;break;
             case '=':if(lp(l)=='='){la(l);t.k=TK_EQ;}else t.k=TK_ASGN;break;
             case '(':t.k=TK_LP2;break;case ')':t.k=TK_RP;break;
             case '{':t.k=TK_LB;break; case '}':t.k=TK_RB;break;
             case '[':t.k=TK_LBK;break;case ']':t.k=TK_RBK;break;
             case ';':t.k=TK_SEMI;break;case ':':t.k=TK_COL;break;
             case ',':t.k=TK_COM;break; case '#':t.k=TK_HASH;break;
             case '.':t.k=TK_DOT;break;
             default:t.k=TK_UNK;WARN(ln,cl,"unexpected char '%c'",c);break;
         }
         lpush(l,t);}
    }
    {Token t;t.k=TK_EOF;t.ln=l->ln;t.cl=l->cl;t.sv=0;t.iv=0;t.fv=0;lpush(l,t);}
}

/* ---------- SECTION 6: AST ---------- */
typedef enum{
    AN_BLOCK,AN_VDECL,AN_IF,AN_LOOP,AN_FOR,AN_BRK,AN_SKP,
    AN_RET,AN_PV,AN_PS,AN_PX,AN_FN,AN_ST,AN_IM,AN_ASM,AN_XSTMT,AN_FF,
    AN_SYSCALL,  /* SC(num, a,b,c,d,e,f) */
    AN_INT,AN_FLT,AN_CHR,AN_STR,AN_BOOL,AN_NULL,AN_ID,
    AN_BOP,AN_UOP,AN_CALL,AN_IDX,AN_FLD,AN_ARW,AN_DEREF,AN_ADDR,
    AN_ALLOC,AN_CAST,AN_SZ,AN_ASGN
}AN;
typedef struct Node Node;
typedef struct{Node**s;int n,cap;}Blk;
typedef struct{char*name;Type*type;Node*init;}VD;
typedef struct{Node*tgt,*val;TK op;}Asgn;
typedef struct{Node*cond,*then;Node**econd,**eblk;int nelf;Node*el;}If;
typedef struct{Node*cond,*body;}Loop;
typedef struct{Node*init,*cond,*post,*body;}For;
typedef struct{Node*val;}Ret;
typedef struct{char*name;Type*ret;char**pn;Type**pt;int np;Node*body;bool8 exp,va;}Fn;
typedef struct{char*name;TF*fields;}St;
typedef struct{char*path;}Im;
typedef struct{char*code;}Asm;
typedef struct{Node*expr;}FF;
typedef struct{Node*l,*r;TK op;}Bop;
typedef struct{Node*op;TK k;bool8 post;}Uop;
typedef struct{Node*fn;Node**args;int na;}Call;
typedef struct{Node*arr,*idx;}Idx;
typedef struct{Node*obj;char*fld;}Fld;
typedef struct{Node*ptr;char*fld;}Arw;
typedef struct{Node*sz;Type*type;}Alloc;
typedef struct{Type*to;Node*expr;}Cast;
typedef struct{Node*args[6];Node*num;}Sc; /* SC syscall */
struct Node{
    AN k;int ln,cl;Type*rt;
    union{
        i64 iv;double fv;char*sv;bool8 bv;
        Blk blk;VD vd;Asgn asgn;If ifs;Loop lp;For fr;Ret ret;
        Fn fn;St st;Im im;Asm as;FF ff;Bop bop;Uop uop;Call call;
        Idx idx;Fld fld;Arw arw;Alloc al;Cast ct;Type*sztype;char*id;
        Sc sc;
    };
};
static Arena g_ast;
static Node*nn(AN k,int l,int c){Node*n=arena_alloc(&g_ast,sizeof*n);n->k=k;n->ln=l;n->cl=c;n->rt=0;return n;}

/* ---------- SECTION 7: PARSER ---------- */
typedef struct{Token*t;u32 pos,n;Arena*a;}Par;
static Token*pp(Par*p){return&p->t[p->pos];}
static Token*pp2(Par*p){return p->pos+1<p->n?&p->t[p->pos+1]:&p->t[p->n-1];}
static Token*pa(Par*p){Token*t=&p->t[p->pos];if(p->pos+1<p->n)p->pos++;return t;}
static bool8 pc(Par*p,TK k){return pp(p)->k==k;}
static bool8 pm(Par*p,TK k){if(pc(p,k)){pa(p);return 1;}return 0;}
static Token*pe(Par*p,TK k,const char*m){
    if(!pc(p,k)){Token*t=pp(p);FATAL(t->ln,t->cl,"expected %s",m);}return pa(p);}

static Node*pexpr(Par*p);
static Node*pstmt(Par*p);

static Type*ptype(Par*p){
    Token*t=pa(p);
    switch(t->k){
        case TK_TVD:return TV;case TK_TBL:return TB;
        case TK_TI8:return TI8;case TK_TI16:return TI16;case TK_TI32:return TI32;case TK_TI64:return TI64;
        case TK_TU8:return TU8;case TK_TU16:return TU16;case TK_TU32:return TU32;case TK_TU64:return TU64;
        case TK_TF32:return TF32;case TK_TF64:return TF64;case TK_TCH:return TCH;
        case TK_TSTR:return tptr(TCH);
        case TK_TPT:{Type*b=TV;if(pc(p,TK_LT)){pa(p);b=ptype(p);pe(p,TK_GT,">");}return tptr(b);}
        case TK_ID:{Type*ty=tnew(TY_STRUCT);ty->name=t->sv;return ty;}
        default:FATAL(t->ln,t->cl,"expected type");return TV;
    }
}
static Node*prim(Par*p){
    Token*t=pp(p);Node*n;
    switch(t->k){
        case TK_INT: pa(p);n=nn(AN_INT,t->ln,t->cl);n->iv=t->iv;return n;
        case TK_FLT: pa(p);n=nn(AN_FLT,t->ln,t->cl);n->fv=t->fv;return n;
        case TK_CHR: pa(p);n=nn(AN_CHR,t->ln,t->cl);n->iv=t->iv;return n;
        case TK_STR: pa(p);n=nn(AN_STR,t->ln,t->cl);n->sv=t->sv;return n;
        case TK_TR:  pa(p);n=nn(AN_BOOL,t->ln,t->cl);n->bv=1;return n;
        case TK_FL_K:pa(p);n=nn(AN_BOOL,t->ln,t->cl);n->bv=0;return n;
        case TK_NL:  pa(p);return nn(AN_NULL,t->ln,t->cl);
        case TK_ID:  pa(p);n=nn(AN_ID,t->ln,t->cl);n->id=t->sv;return n;
        case TK_LP2:{Node*in;pa(p);in=pexpr(p);pe(p,TK_RP,")");return in;}
        case TK_AMP: pa(p);n=nn(AN_ADDR,t->ln,t->cl);n->uop.op=prim(p);n->uop.k=TK_AMP;n->uop.post=0;return n;
        case TK_DR:  pa(p);n=nn(AN_DEREF,t->ln,t->cl);n->uop.op=prim(p);n->uop.k=TK_STAR;n->uop.post=0;return n;
        case TK_AL:  pa(p);n=nn(AN_ALLOC,t->ln,t->cl);n->al.type=ptype(p);n->al.sz=pexpr(p);return n;
        case TK_SZ:  pa(p);pe(p,TK_LP2,"(");n=nn(AN_SZ,t->ln,t->cl);n->sztype=ptype(p);pe(p,TK_RP,")");return n;
        case TK_CT:  pa(p);pe(p,TK_LP2,"(");n=nn(AN_CAST,t->ln,t->cl);
                     n->ct.to=ptype(p);pe(p,TK_COM,",");n->ct.expr=pexpr(p);pe(p,TK_RP,")");return n;
        case TK_SC:{
            /* SC(num, a, b, c, d, e, f) — up to 7 args: syscall number + 6 args */
            int i;
            pa(p);pe(p,TK_LP2,"(");
            n=nn(AN_SYSCALL,t->ln,t->cl);
            n->sc.num=pexpr(p);
            for(i=0;i<6;i++){
                n->sc.args[i]=0;
                if(pm(p,TK_COM))n->sc.args[i]=pexpr(p);
                else break;
            }
            /* consume any remaining commas+args silently */
            while(pm(p,TK_COM))pexpr(p);
            pe(p,TK_RP,")");return n;
        }
        case TK_MINUS:case TK_BANG:case TK_TILDE:case TK_INC:case TK_DEC:{
            TK k=t->k;pa(p);n=nn(AN_UOP,t->ln,t->cl);
            n->uop.k=k;n->uop.op=prim(p);n->uop.post=0;return n;}
        default:FATAL(t->ln,t->cl,"unexpected token in expr");return 0;
    }
}
static Node*postfix(Par*p){
    Node*n=prim(p);
    while(1){
        Token*t=pp(p);
        if(t->k==TK_LP2){
            Node*c=nn(AN_CALL,t->ln,t->cl);c->call.fn=n;c->call.args=0;c->call.na=0;
            pa(p);
            if(!pc(p,TK_RP)){
                int cap=4;c->call.args=arena_alloc(p->a,sizeof(Node*)*cap);
                do{if(c->call.na>=cap){Node**old=c->call.args;int oc=cap;cap*=2;
                       c->call.args=arena_alloc(p->a,sizeof(Node*)*cap);memcpy(c->call.args,old,sizeof(Node*)*oc);}
                   c->call.args[c->call.na++]=pexpr(p);}while(pm(p,TK_COM));
            }
            pe(p,TK_RP,")");n=c;
        }else if(t->k==TK_LBK){
            Node*i=nn(AN_IDX,t->ln,t->cl);pa(p);i->idx.arr=n;i->idx.idx=pexpr(p);pe(p,TK_RBK,"]");n=i;
        }else if(t->k==TK_DOT){
            Node*f=nn(AN_FLD,t->ln,t->cl);pa(p);f->fld.obj=n;f->fld.fld=pe(p,TK_ID,"field")->sv;n=f;
        }else if(t->k==TK_ARR){
            Node*a=nn(AN_ARW,t->ln,t->cl);pa(p);a->arw.ptr=n;a->arw.fld=pe(p,TK_ID,"field")->sv;n=a;
        }else if(t->k==TK_INC||t->k==TK_DEC){
            Node*u=nn(AN_UOP,t->ln,t->cl);pa(p);u->uop.k=t->k;u->uop.op=n;u->uop.post=1;n=u;
        }else break;
    }
    return n;
}
static int bprec(TK k){
    switch(k){case TK_OR:return 1;case TK_AND:return 2;case TK_PIPE:return 3;
        case TK_CARET:return 4;case TK_AMP:return 5;
        case TK_EQ:case TK_NEQ:return 6;
        case TK_LT:case TK_GT:case TK_LTE:case TK_GTE:return 7;
        case TK_SHL:case TK_SHR:return 8;
        case TK_PLUS:case TK_MINUS:return 9;
        case TK_STAR:case TK_SLASH:case TK_PCT:return 10;
        default:return -1;}
}
static Node*pbinop(Par*p,int mp){
    Node*l=postfix(p);
    while(1){Token*t=pp(p);int pr=bprec(t->k);if(pr<mp)break;
        {TK op=t->k;int ln=t->ln,cl=t->cl;Node*r,*b;
         pa(p);r=pbinop(p,pr+1);b=nn(AN_BOP,ln,cl);b->bop.l=l;b->bop.r=r;b->bop.op=op;l=b;}}
    return l;
}
static Node*pexpr(Par*p){
    Node*l=pbinop(p,0);Token*t=pp(p);
    if(t->k==TK_ASGN||t->k==TK_PASGN||t->k==TK_MASGN||t->k==TK_SASGN||t->k==TK_DASGN){
        TK op=t->k;int ln=t->ln,cl=t->cl;Node*r,*a;
        pa(p);r=pexpr(p);a=nn(AN_ASGN,ln,cl);a->asgn.tgt=l;a->asgn.val=r;a->asgn.op=op;return a;}
    return l;
}
static Node*pblock(Par*p){
    Token*t=pe(p,TK_LB,"{");Node*b=nn(AN_BLOCK,t->ln,t->cl);b->blk.s=0;b->blk.n=0;b->blk.cap=0;
    while(!pc(p,TK_RB)&&!pc(p,TK_EOF)){
        Node*s=pstmt(p);if(!s)continue;
        if(b->blk.n>=b->blk.cap){int nc=b->blk.cap?b->blk.cap*2:8;Node**old=b->blk.s;
            b->blk.s=arena_alloc(p->a,sizeof(Node*)*nc);if(old)memcpy(b->blk.s,old,sizeof(Node*)*b->blk.n);b->blk.cap=nc;}
        b->blk.s[b->blk.n++]=s;
    }
    pe(p,TK_RB,"}");return b;
}
static Node*pstmt(Par*p){
    Token*t=pp(p);Node*n;
    switch(t->k){
        case TK_V:
            pa(p);n=nn(AN_VDECL,t->ln,t->cl);
            n->vd.type=ptype(p);n->vd.name=pe(p,TK_ID,"var name")->sv;n->vd.init=0;
            if(pm(p,TK_ASGN))n->vd.init=pexpr(p);pm(p,TK_SEMI);return n;
        case TK_RT:
            pa(p);n=nn(AN_RET,t->ln,t->cl);n->ret.val=0;
            if(!pc(p,TK_SEMI)&&!pc(p,TK_RB))n->ret.val=pexpr(p);pm(p,TK_SEMI);return n;
        case TK_PV:{Token*nm;Node*id;pa(p);n=nn(AN_PV,t->ln,t->cl);
            nm=pe(p,TK_ID,"var name");id=nn(AN_ID,nm->ln,nm->cl);id->id=nm->sv;
            n->uop.op=id;pm(p,TK_SEMI);return n;}
        case TK_PS:pa(p);n=nn(AN_PS,t->ln,t->cl);n->sv=pe(p,TK_STR,"string")->sv;pm(p,TK_SEMI);return n;
        case TK_P: pa(p);n=nn(AN_PX,t->ln,t->cl);n->uop.op=pexpr(p);pm(p,TK_SEMI);return n;
        case TK_IF:{
            pa(p);n=nn(AN_IF,t->ln,t->cl);
            n->ifs.cond=pexpr(p);n->ifs.then=pblock(p);
            n->ifs.econd=0;n->ifs.eblk=0;n->ifs.nelf=0;n->ifs.el=0;
            while(pc(p,TK_ELF)){int ec;Node**nc,**nb;pa(p);ec=n->ifs.nelf;
                nc=arena_alloc(p->a,sizeof(Node*)*(ec+1));nb=arena_alloc(p->a,sizeof(Node*)*(ec+1));
                if(ec){memcpy(nc,n->ifs.econd,sizeof(Node*)*ec);memcpy(nb,n->ifs.eblk,sizeof(Node*)*ec);}
                nc[ec]=pexpr(p);nb[ec]=pblock(p);n->ifs.econd=nc;n->ifs.eblk=nb;n->ifs.nelf++;}
            if(pc(p,TK_EL)){pa(p);n->ifs.el=pblock(p);}return n;}
        case TK_LP:
            pa(p);n=nn(AN_LOOP,t->ln,t->cl);n->lp.cond=pexpr(p);n->lp.body=pblock(p);return n;
        case TK_FR:
            pa(p);n=nn(AN_FOR,t->ln,t->cl);
            n->fr.init=pstmt(p);n->fr.cond=pexpr(p);pm(p,TK_SEMI);
            n->fr.post=pexpr(p);n->fr.body=pblock(p);return n;
        case TK_BK:pa(p);pm(p,TK_SEMI);return nn(AN_BRK,t->ln,t->cl);
        case TK_SK:pa(p);pm(p,TK_SEMI);return nn(AN_SKP,t->ln,t->cl);
        case TK_FN:case TK_EX:{
            bool8 exp=(t->k==TK_EX);if(exp){pa(p);t=pp(p);}pa(p);
            n=nn(AN_FN,t->ln,t->cl);n->fn.exp=exp;
            n->fn.name=pe(p,TK_ID,"fn name")->sv;
            n->fn.pn=0;n->fn.pt=0;n->fn.np=0;n->fn.va=0;
            pe(p,TK_LP2,"(");
            if(!pc(p,TK_RP)){
                int cap=4;char**pn=arena_alloc(p->a,sizeof(char*)*cap);Type**pt=arena_alloc(p->a,sizeof(Type*)*cap);
                do{Type*ty;char*nm;
                   if(pc(p,TK_DOT)&&pp2(p)->k==TK_DOT){pa(p);pa(p);pa(p);n->fn.va=1;break;}
                   ty=ptype(p);nm=pe(p,TK_ID,"param")->sv;
                   if(n->fn.np>=cap){char**on=pn;Type**ot=pt;cap*=2;
                       pn=arena_alloc(p->a,sizeof(char*)*cap);pt=arena_alloc(p->a,sizeof(Type*)*cap);
                       memcpy(pn,on,sizeof(char*)*n->fn.np);memcpy(pt,ot,sizeof(Type*)*n->fn.np);}
                   pt[n->fn.np]=ty;pn[n->fn.np]=nm;n->fn.np++;
                }while(pm(p,TK_COM));
                n->fn.pn=pn;n->fn.pt=pt;
            }
            pe(p,TK_RP,")");n->fn.ret=TV;if(!pc(p,TK_LB))n->fn.ret=ptype(p);
            n->fn.body=pblock(p);return n;}
        case TK_ST:{TF*last;pa(p);n=nn(AN_ST,t->ln,t->cl);
            n->st.name=pe(p,TK_ID,"struct name")->sv;n->st.fields=0;pe(p,TK_LB,"{");last=0;
            while(!pc(p,TK_RB)&&!pc(p,TK_EOF)){
                TF*f=arena_alloc(p->a,sizeof*f);f->type=ptype(p);f->name=pe(p,TK_ID,"field")->sv;f->next=0;
                pm(p,TK_SEMI);if(!last)n->st.fields=f;else last->next=f;last=f;}
            pe(p,TK_RB,"}");return n;}
        case TK_IM:pa(p);n=nn(AN_IM,t->ln,t->cl);n->im.path=pe(p,TK_STR,"path")->sv;pm(p,TK_SEMI);return n;
        case TK_ASM:{pa(p);n=nn(AN_ASM,t->ln,t->cl);pe(p,TK_LB,"{");
            {char buf[8192];u32 bi=0;int d=1;
             while(!pc(p,TK_EOF)){Token*at=pa(p);
                 if(at->k==TK_LB){d++;if(bi<sizeof(buf)-2)buf[bi++]='{';}
                 else if(at->k==TK_RB){d--;if(!d)break;if(bi<sizeof(buf)-2)buf[bi++]='}';}
                 else if(at->sv){u32 sl=(u32)strlen(at->sv);if(bi+sl+2<sizeof(buf)){memcpy(buf+bi,at->sv,sl);bi+=sl;buf[bi++]=' ';}}
                 else if(at->k==TK_INT&&bi+32<sizeof(buf))bi+=(u32)sprintf(buf+bi,"%lld ",(long long)at->iv);}
             buf[bi]=0;n->as.code=astrdup(p->a,buf);}return n;}
        case TK_FF:pa(p);n=nn(AN_FF,t->ln,t->cl);n->ff.expr=pexpr(p);pm(p,TK_SEMI);return n;
        /* SC as statement: SC(num,...); */
        case TK_SC:{
            Node*e=pexpr(p);pm(p,TK_SEMI);
            n=nn(AN_XSTMT,e->ln,e->cl);n->uop.op=e;return n;}
        default:{Node*e=pexpr(p);pm(p,TK_SEMI);n=nn(AN_XSTMT,e->ln,e->cl);n->uop.op=e;return n;}
    }
}
static Node*pprog(Par*p){
    Node*prog=nn(AN_BLOCK,1,1);prog->blk.s=0;prog->blk.n=0;prog->blk.cap=0;
    while(!pc(p,TK_EOF)){
        Node*s=pstmt(p);if(!s)continue;
        if(prog->blk.n>=prog->blk.cap){int nc=prog->blk.cap?prog->blk.cap*2:16;Node**old=prog->blk.s;
            prog->blk.s=arena_alloc(p->a,sizeof(Node*)*nc);if(old)memcpy(prog->blk.s,old,sizeof(Node*)*prog->blk.n);prog->blk.cap=nc;}
        prog->blk.s[prog->blk.n++]=s;
    }
    return prog;
}

/* ---------- SECTION 8: SYMBOL TABLE ---------- */
typedef enum{SK_VAR,SK_FN,SK_STRUCT,SK_PARAM}SK;
typedef struct Sym Sym;
struct Sym{char*name;SK k;Type*type;int depth;i32 stk;u32 doff;bool8 glob;Sym*next;};
#define HTAB 512
typedef struct Scp Scp;
struct Scp{Sym*b[HTAB];Scp*up;int depth;};
typedef struct{Scp*cur;Arena*a;}SymTab;
static void st_init(SymTab*s,Arena*a){s->a=a;s->cur=0;}
static void st_push(SymTab*s){Scp*c=arena_alloc(s->a,sizeof*c);memset(c->b,0,sizeof c->b);c->up=s->cur;c->depth=s->cur?s->cur->depth+1:0;s->cur=c;}
static void st_pop(SymTab*s){if(s->cur)s->cur=s->cur->up;}
static u32 shash(const char*s){u32 h=2166136261u;while(*s){h^=(u8)*s++;h*=16777619u;}return h%HTAB;}
static Sym*st_find(SymTab*s,const char*n){Scp*c=s->cur;u32 h=shash(n);
    while(c){Sym*sy=c->b[h];while(sy){if(!strcmp(sy->name,n))return sy;sy=sy->next;}c=c->up;}return 0;}
static Sym*st_find_local(SymTab*s,const char*n){u32 h=shash(n);Sym*sy=s->cur->b[h];
    while(sy){if(!strcmp(sy->name,n))return sy;sy=sy->next;}return 0;}
static Sym*st_def(SymTab*s,const char*n,SK k,Type*t){
    u32 h;Sym*sy;if(st_find_local(s,n))return 0;
    h=shash(n);sy=arena_alloc(s->a,sizeof*sy);sy->name=astrdup(s->a,n);
    sy->k=k;sy->type=t;sy->depth=s->cur->depth;sy->stk=0;sy->doff=0;
    sy->glob=(s->cur->up==0);sy->next=s->cur->b[h];s->cur->b[h]=sy;return sy;}

/* ---------- SECTION 9: SEMANTIC ---------- */
typedef struct{SymTab*s;Arena*a;Type*fnret;int ldepth;}Sem;
static void sem_fix(Sem*sm,Type**pt){
    Type*t=*pt;if(!t)return;
    if((t->k==TY_PTR||t->k==TY_ARRAY)&&t->base)sem_fix(sm,&t->base);
    if(t->k==TY_STRUCT&&!t->fields&&t->name){Sym*s=st_find(sm->s,t->name);if(s&&s->k==SK_STRUCT)*pt=s->type;}}
static Type*sem_e(Sem*sm,Node*n);
static void sem_s(Sem*sm,Node*n);
static void sem_blk(Sem*sm,Node*n);
static Type*sem_e(Sem*sm,Node*n){
    if(!n)return TV;
    switch(n->k){
        case AN_INT: n->rt=TI64;return TI64;
        case AN_FLT: n->rt=TF64;return TF64;
        case AN_CHR: n->rt=TCH;return TCH;
        case AN_BOOL:n->rt=TB;return TB;
        case AN_NULL:n->rt=tptr(TV);return n->rt;
        case AN_STR: n->rt=tptr(TCH);return n->rt;
        case AN_ID:{Sym*s=st_find(sm->s,n->id);
            if(!s){ERR(n->ln,n->cl,"undefined '%s'",n->id);n->rt=TUN;return TUN;}
            n->rt=s->type;return s->type;}
        case AN_BOP:{Type*lt=sem_e(sm,n->bop.l);Type*rt=sem_e(sm,n->bop.r);
            switch(n->bop.op){case TK_EQ:case TK_NEQ:case TK_LT:case TK_GT:
                case TK_LTE:case TK_GTE:case TK_AND:case TK_OR:n->rt=TB;return TB;default:break;}
            if(tis_flt(lt)||tis_flt(rt))n->rt=TF64;
            else if(lt->k==TY_PTR||rt->k==TY_PTR)n->rt=(lt->k==TY_PTR)?lt:rt;
            else if(lt->k==TY_I64||rt->k==TY_I64)n->rt=TI64;
            else n->rt=lt;return n->rt;}
        case AN_UOP:{if(n->uop.k==TK_INC||n->uop.k==TK_DEC){Type*t=sem_e(sm,n->uop.op);n->rt=t;return t;}
            {Type*t=sem_e(sm,n->uop.op);n->rt=(n->uop.k==TK_BANG)?TB:t;return n->rt;}}
        case AN_ADDR:{Type*t=sem_e(sm,n->uop.op);n->rt=tptr(t);return n->rt;}
        case AN_DEREF:{Type*t=sem_e(sm,n->uop.op);
            if(t->k!=TY_PTR&&t->k!=TY_UNK)ERR(n->ln,n->cl,"DR on non-pointer '%s'",tname(t));
            n->rt=(t->k==TY_PTR)?t->base:TUN;return n->rt;}
        case AN_SYSCALL:{int i;for(i=0;i<6;i++)if(n->sc.args[i])sem_e(sm,n->sc.args[i]);
            sem_e(sm,n->sc.num);n->rt=TI64;return TI64;}
        case AN_CALL:{int i;Type*ret=TUN;
            if(n->call.fn->k==AN_ID){Sym*s=st_find(sm->s,n->call.fn->id);
                if(!s)ERR(n->call.fn->ln,n->call.fn->cl,"call to undefined '%s'",n->call.fn->id);
                else if(s->type&&s->type->k==TY_FN){ret=s->type->ret;
                    if(n->call.na<s->type->pcount)WARN(n->ln,n->cl,"'%s': expected %d args",n->call.fn->id,s->type->pcount);}
                else if(s->type&&s->type->k!=TY_FN)ERR(n->ln,n->cl,"'%s' not a function",n->call.fn->id);}
            else{Type*ct=sem_e(sm,n->call.fn);if(ct&&ct->k==TY_FN)ret=ct->ret;}
            for(i=0;i<n->call.na;i++)sem_e(sm,n->call.args[i]);n->rt=ret;return ret;}
        case AN_IDX:{Type*at=sem_e(sm,n->idx.arr);sem_e(sm,n->idx.idx);
            if(at->k==TY_PTR||at->k==TY_ARRAY)n->rt=at->base;
            else{ERR(n->ln,n->cl,"index of non-array");n->rt=TUN;}return n->rt;}
        case AN_FLD:{Type*ot=sem_e(sm,n->fld.obj);TF*f;
            if(ot->k!=TY_STRUCT){ERR(n->ln,n->cl,"field on non-struct");n->rt=TUN;return TUN;}
            for(f=ot->fields;f;f=f->next)if(!strcmp(f->name,n->fld.fld)){n->rt=f->type;return f->type;}
            ERR(n->ln,n->cl,"no field '%s'",n->fld.fld);n->rt=TUN;return TUN;}
        case AN_ARW:{Type*pt=sem_e(sm,n->arw.ptr);Type*st=(pt->k==TY_PTR)?pt->base:pt;TF*f;
            if(!st||st->k!=TY_STRUCT){ERR(n->ln,n->cl,"-> on non-struct-ptr");n->rt=TUN;return TUN;}
            for(f=st->fields;f;f=f->next)if(!strcmp(f->name,n->arw.fld)){n->rt=f->type;return f->type;}
            ERR(n->ln,n->cl,"no field '%s'",n->arw.fld);n->rt=TUN;return TUN;}
        case AN_ALLOC:sem_fix(sm,&n->al.type);sem_e(sm,n->al.sz);n->rt=tptr(n->al.type);return n->rt;
        case AN_CAST:sem_fix(sm,&n->ct.to);sem_e(sm,n->ct.expr);n->rt=n->ct.to;return n->rt;
        case AN_SZ:sem_fix(sm,&n->sztype);n->rt=TU64;return TU64;
        case AN_ASGN:{Type*vt;sem_e(sm,n->asgn.tgt);vt=sem_e(sm,n->asgn.val);n->rt=vt;return vt;}
        default:n->rt=TUN;return TUN;
    }
}
static void sem_s(Sem*sm,Node*n){
    if(!n)return;
    switch(n->k){
        case AN_BLOCK:sem_blk(sm,n);return;
        case AN_VDECL:{Sym*s;sem_fix(sm,&n->vd.type);if(n->vd.init)sem_e(sm,n->vd.init);
            s=st_def(sm->s,n->vd.name,SK_VAR,n->vd.type);if(!s)ERR(n->ln,n->cl,"redef '%s'",n->vd.name);return;}
        case AN_XSTMT:case AN_PV:case AN_PX:sem_e(sm,n->uop.op);return;
        case AN_PS:return;
        case AN_RET:if(n->ret.val){Type*rt=sem_e(sm,n->ret.val);
            if(sm->fnret&&sm->fnret->k!=TY_VOID&&!teq(rt,sm->fnret))WARN(n->ln,n->cl,"return type mismatch");}return;
        case AN_IF:{int i;sem_e(sm,n->ifs.cond);sem_blk(sm,n->ifs.then);
            for(i=0;i<n->ifs.nelf;i++){sem_e(sm,n->ifs.econd[i]);sem_blk(sm,n->ifs.eblk[i]);}
            if(n->ifs.el)sem_blk(sm,n->ifs.el);return;}
        case AN_LOOP:sem_e(sm,n->lp.cond);sm->ldepth++;sem_blk(sm,n->lp.body);sm->ldepth--;return;
        case AN_FOR:st_push(sm->s);sem_s(sm,n->fr.init);sem_e(sm,n->fr.cond);sem_e(sm,n->fr.post);
            sm->ldepth++;sem_blk(sm,n->fr.body);sm->ldepth--;st_pop(sm->s);return;
        case AN_BRK:if(!sm->ldepth)WARN(n->ln,n->cl,"BK outside loop");return;
        case AN_SKP:if(!sm->ldepth)WARN(n->ln,n->cl,"SK outside loop");return;
        case AN_FN:{int i;Type*fnt,*old;
            sem_fix(sm,&n->fn.ret);for(i=0;i<n->fn.np;i++)sem_fix(sm,&n->fn.pt[i]);
            fnt=tnew(TY_FN);fnt->ret=n->fn.ret;fnt->pcount=n->fn.np;fnt->ptypes=n->fn.pt;
            if(!st_def(sm->s,n->fn.name,SK_FN,fnt))ERR(n->ln,n->cl,"redef fn '%s'",n->fn.name);
            st_push(sm->s);for(i=0;i<n->fn.np;i++)st_def(sm->s,n->fn.pn[i],SK_PARAM,n->fn.pt[i]);
            old=sm->fnret;sm->fnret=n->fn.ret;sem_blk(sm,n->fn.body);sm->fnret=old;st_pop(sm->s);return;}
        case AN_ST:{Type*st=tnew(TY_STRUCT);st->name=n->st.name;st->fields=n->st.fields;
            if(!st_def(sm->s,n->st.name,SK_STRUCT,st))ERR(n->ln,n->cl,"redef struct '%s'",n->st.name);return;}
        case AN_FF:sem_e(sm,n->ff.expr);return;
        case AN_IM:case AN_ASM:return;
        case AN_SYSCALL:sem_e(sm,n);return;
        default:return;
    }
}
static void sem_blk(Sem*sm,Node*n){int i;st_push(sm->s);for(i=0;i<n->blk.n;i++)sem_s(sm,n->blk.s[i]);st_pop(sm->s);}

/* ---------- SECTION 10: IR ---------- */
typedef enum{
    IO_NOP,IO_LBL,IO_STR,IO_LOAD,IO_STORE,IO_ADDR,IO_DEREF,
    IO_ADD,IO_SUB,IO_MUL,IO_DIV,IO_MOD,IO_AND,IO_OR,IO_XOR,IO_NOT,IO_NEG,IO_SHL,IO_SHR,
    IO_EQ,IO_NEQ,IO_LT,IO_GT,IO_LTE,IO_GTE,IO_LAND,IO_LOR,
    IO_JMP,IO_JZ,IO_JNZ,IO_CALL,IO_RET,IO_ALLOCA,IO_PARAM,
    IO_MALLOC,IO_FREE,IO_CAST,IO_FLD,IO_ASM,
    IO_PINT,IO_PSTR,IO_PFLT,IO_PCHR,
    IO_FN0,IO_FN1,
    IO_SYSCALL  /* raw syscall: src1=num, args[0..5] */
}IOp;
typedef enum{IV_REG,IV_CINT,IV_CFLT,IV_LBL,IV_STR,IV_NONE}IVK;
typedef struct{IVK k;u32 reg;i64 iv;double fv;char*sv;Type*type;}IV;
static IV ivnone(void){IV v;v.k=IV_NONE;v.reg=0;v.iv=0;v.fv=0;v.sv=0;v.type=0;return v;}
typedef struct{
    IOp op;IV dst,s1,s2;char*lbl;char*fn;
    int na;IV*args;Type*ctype;Type*atype;u32 fidx;char*asmcode;
}II;
typedef struct{II*ii;u32 n,cap,nreg,nlbl;Arena*a;}IRB;
static void ir_init(IRB*b,Arena*a){b->ii=0;b->n=b->cap=0;b->nreg=b->nlbl=0;b->a=a;}
static II*ir_e(IRB*b){II*i;if(b->n>=b->cap){b->cap=b->cap?b->cap*2:256;b->ii=realloc(b->ii,sizeof(II)*b->cap);}
    i=&b->ii[b->n++];memset(i,0,sizeof*i);return i;}
static IV ivreg(IRB*b,Type*t){IV v;v.k=IV_REG;v.reg=b->nreg++;v.type=t;v.iv=0;v.fv=0;v.sv=0;return v;}
static char*ivlbl(IRB*b,const char*pfx){char buf[64];sprintf(buf,"%s_%u",pfx,b->nlbl++);return astrdup(b->a,buf);}
static IV ivci(i64 v,Type*t){IV r;r.k=IV_CINT;r.iv=v;r.type=t;r.reg=0;r.fv=0;r.sv=0;return r;}
static IV ivcf(double v,Type*t){IV r;r.k=IV_CFLT;r.fv=v;r.type=t;r.reg=0;r.iv=0;r.sv=0;return r;}
static IV ivsv(char*s){IV r;r.k=IV_STR;r.sv=s;r.type=0;r.reg=0;r.iv=0;r.fv=0;return r;}
#define IMAP 512
typedef struct{char*name;IV val;}IME;
typedef struct IScp IScp;
struct IScp{IME e[IMAP];int n;IScp*up;};
static IScp*iscpnew(Arena*a,IScp*up){IScp*s=arena_alloc(a,sizeof*s);s->n=0;s->up=up;return s;}
static void iscpset(IScp*s,const char*n,IV v){int i;
    for(i=0;i<s->n;i++)if(!strcmp(s->e[i].name,n)){s->e[i].val=v;return;}
    if(s->n<IMAP){s->e[s->n].name=(char*)n;s->e[s->n].val=v;s->n++;}}
static bool8 iscpget(IScp*s,const char*n,IV*out){IScp*c=s;int i;
    while(c){for(i=0;i<c->n;i++)if(!strcmp(c->e[i].name,n)){*out=c->e[i].val;return 1;}c=c->up;}return 0;}
typedef struct LL{char*brk,*cont;struct LL*up;}LL;
typedef struct{IRB*b;Arena*a;IScp*sc;LL*loops;}IRL;
static IV lower_e(IRL*l,Node*n);
static void lower_s(IRL*l,Node*n);
static IV lower_addr(IRL*l,Node*n);
static u32 foff(Type*st,const char*nm){u32 o=0;TF*f;if(!st)return 0;
    for(f=st->fields;f;f=f->next){if(!strcmp(f->name,nm))return o;o+=tsz(f->type);}return 0;}
static IV lower_addr(IRL*l,Node*n){
    IRB*b=l->b;if(!n)return ivnone();
    switch(n->k){
        case AN_ID:{IV a;if(iscpget(l->sc,n->id,&a))return a;return ivnone();}
        case AN_DEREF:return lower_e(l,n->uop.op);
        case AN_IDX:{IV av=lower_e(l,n->idx.arr),iv=lower_e(l,n->idx.idx);
            u32 esz=n->rt?tsz(n->rt):8;IV off,ptr;II*m,*a;if(!esz)esz=1;
            off=ivreg(b,TU64);m=ir_e(b);m->op=IO_MUL;m->dst=off;m->s1=iv;m->s2=ivci(esz,TU64);
            ptr=ivreg(b,tptr(n->rt?n->rt:TU8));a=ir_e(b);a->op=IO_ADD;a->dst=ptr;a->s1=av;a->s2=off;return ptr;}
        case AN_ARW:{IV pv=lower_e(l,n->arw.ptr);Type*pt=n->arw.ptr->rt;
            Type*st=(pt&&pt->k==TY_PTR)?pt->base:pt;
            u32 o=(st&&st->k==TY_STRUCT)?foff(st,n->arw.fld):0;
            IV fr=ivreg(b,tptr(n->rt?n->rt:TU8));II*f=ir_e(b);f->op=IO_FLD;f->dst=fr;f->s1=pv;f->fidx=o;return fr;}
        case AN_FLD:{IV ov=lower_addr(l,n->fld.obj);Type*ot=n->fld.obj->rt;
            u32 o=(ot&&ot->k==TY_STRUCT)?foff(ot,n->fld.fld):0;
            IV fr=ivreg(b,tptr(n->rt?n->rt:TU8));II*f=ir_e(b);f->op=IO_FLD;f->dst=fr;f->s1=ov;f->fidx=o;return fr;}
        default:return ivnone();
    }
}
static IV lower_e(IRL*l,Node*n){
    IRB*b=l->b;II*ins;IV dst;if(!n)return ivnone();
    switch(n->k){
        case AN_INT:  return ivci(n->iv,n->rt?n->rt:TI64);
        case AN_FLT:  return ivcf(n->fv,n->rt?n->rt:TF64);
        case AN_CHR:  return ivci(n->iv,TCH);
        case AN_BOOL: return ivci(n->bv?1:0,TB);
        case AN_NULL: return ivci(0,tptr(TV));
        case AN_STR:  dst=ivreg(b,tptr(TCH));ins=ir_e(b);ins->op=IO_STR;ins->dst=dst;ins->s1=ivsv(n->sv);return dst;
        case AN_ID:{IV a;Type*t;
            if(!iscpget(l->sc,n->id,&a))return ivci(0,n->rt?n->rt:TI64);
            t=n->rt;if(t&&(t->k==TY_STRUCT||t->k==TY_ARRAY||t->k==TY_FN))return a;
            dst=ivreg(b,t?t:TI64);ins=ir_e(b);ins->op=IO_DEREF;ins->dst=dst;ins->s1=a;return dst;}
        case AN_BOP:{IV lv=lower_e(l,n->bop.l),rv=lower_e(l,n->bop.r);
            dst=ivreg(b,n->rt?n->rt:TI64);ins=ir_e(b);
            switch(n->bop.op){
                case TK_PLUS:ins->op=IO_ADD;break;case TK_MINUS:ins->op=IO_SUB;break;
                case TK_STAR:ins->op=IO_MUL;break;case TK_SLASH:ins->op=IO_DIV;break;
                case TK_PCT:ins->op=IO_MOD;break;case TK_AMP:ins->op=IO_AND;break;
                case TK_PIPE:ins->op=IO_OR;break;case TK_CARET:ins->op=IO_XOR;break;
                case TK_SHL:ins->op=IO_SHL;break;case TK_SHR:ins->op=IO_SHR;break;
                case TK_EQ:ins->op=IO_EQ;break;case TK_NEQ:ins->op=IO_NEQ;break;
                case TK_LT:ins->op=IO_LT;break;case TK_GT:ins->op=IO_GT;break;
                case TK_LTE:ins->op=IO_LTE;break;case TK_GTE:ins->op=IO_GTE;break;
                case TK_AND:ins->op=IO_LAND;break;case TK_OR:ins->op=IO_LOR;break;
                default:ins->op=IO_ADD;break;}
            ins->dst=dst;ins->s1=lv;ins->s2=rv;return dst;}
        case AN_UOP:{
            if(n->uop.k==TK_INC||n->uop.k==TK_DEC){
                Type*ot=n->uop.op->rt;IV addr=lower_addr(l,n->uop.op);IV cur,nv;II*ld,*op,*st;
                if(addr.k==IV_NONE)return ivci(0,TI64);
                cur=ivreg(b,ot&&tis_int(ot)?ot:TI64);ld=ir_e(b);ld->op=IO_DEREF;ld->dst=cur;ld->s1=addr;
                nv=ivreg(b,cur.type);op=ir_e(b);op->op=(n->uop.k==TK_INC)?IO_ADD:IO_SUB;
                op->dst=nv;op->s1=cur;op->s2=ivci(1,TI64);
                st=ir_e(b);st->op=IO_STORE;st->s1=addr;st->s2=nv;return n->uop.post?cur:nv;}
            {IV ov=lower_e(l,n->uop.op);dst=ivreg(b,n->rt?n->rt:TI64);ins=ir_e(b);
             switch(n->uop.k){case TK_MINUS:ins->op=IO_NEG;break;case TK_BANG:ins->op=IO_NOT;break;
                 case TK_TILDE:ins->op=IO_XOR;ins->s2=ivci(-1,TI64);break;default:ins->op=IO_NEG;break;}
             ins->dst=dst;ins->s1=ov;return dst;}}
        case AN_ADDR:{IV a=lower_addr(l,n->uop.op);II*cp;if(a.k==IV_NONE)return a;
            dst=ivreg(b,tptr(n->uop.op->rt?n->uop.op->rt:TV));cp=ir_e(b);cp->op=IO_ADDR;cp->dst=dst;cp->s1=a;return dst;}
        case AN_DEREF:{IV pv=lower_e(l,n->uop.op);Type*t=n->rt;
            if(t&&t->k==TY_STRUCT)return pv;
            dst=ivreg(b,t?t:TI64);ins=ir_e(b);ins->op=IO_DEREF;ins->dst=dst;ins->s1=pv;return dst;}
        case AN_ALLOC:{IV szv=lower_e(l,n->al.sz);u32 tsz2=tsz(n->al.type);IV tot;II*mi;
            if(!tsz2)tsz2=1;tot=ivreg(b,TU64);ins=ir_e(b);ins->op=IO_MUL;ins->dst=tot;ins->s1=szv;ins->s2=ivci(tsz2,TU64);
            dst=ivreg(b,n->rt?n->rt:tptr(TV));mi=ir_e(b);mi->op=IO_MALLOC;mi->dst=dst;mi->s1=tot;return dst;}
        case AN_CAST:{IV cv=lower_e(l,n->ct.expr);dst=ivreg(b,n->ct.to);
            ins=ir_e(b);ins->op=IO_CAST;ins->dst=dst;ins->s1=cv;ins->ctype=n->ct.to;return dst;}
        case AN_SZ:return ivci(tsz(n->sztype),TU64);
        case AN_CALL:{int i;IV*args=arena_alloc(b->a,sizeof(IV)*(n->call.na?n->call.na:1));
            for(i=0;i<n->call.na;i++)args[i]=lower_e(l,n->call.args[i]);
            dst=ivreg(b,n->rt?n->rt:TV);ins=ir_e(b);ins->op=IO_CALL;ins->dst=dst;
            ins->fn=(n->call.fn->k==AN_ID)?n->call.fn->id:0;ins->na=n->call.na;ins->args=args;return dst;}
        case AN_IDX:case AN_FLD:case AN_ARW:{IV addr=lower_addr(l,n);Type*t=n->rt;
            if(t&&t->k==TY_STRUCT)return addr;
            dst=ivreg(b,t?t:TI64);ins=ir_e(b);ins->op=IO_DEREF;ins->dst=dst;ins->s1=addr;return dst;}
        case AN_ASGN:{IV rv=lower_e(l,n->asgn.val);IV addr=lower_addr(l,n->asgn.tgt);II*st;
            if(addr.k==IV_NONE)return rv;
            if(n->asgn.op!=TK_ASGN){Type*tt=n->asgn.tgt->rt;IV cur=ivreg(b,tt?tt:TI64);IV res;II*ld,*op;
                ld=ir_e(b);ld->op=IO_DEREF;ld->dst=cur;ld->s1=addr;
                res=ivreg(b,tt?tt:TI64);op=ir_e(b);
                switch(n->asgn.op){case TK_PASGN:op->op=IO_ADD;break;case TK_MASGN:op->op=IO_SUB;break;
                    case TK_SASGN:op->op=IO_MUL;break;case TK_DASGN:op->op=IO_DIV;break;default:op->op=IO_ADD;break;}
                op->dst=res;op->s1=cur;op->s2=rv;st=ir_e(b);st->op=IO_STORE;st->s1=addr;st->s2=res;return res;}
            st=ir_e(b);st->op=IO_STORE;st->s1=addr;st->s2=rv;return rv;}
        case AN_SYSCALL:{
            /* SC(num, a0..a5) -> IO_SYSCALL */
            int i;IV*args=arena_alloc(b->a,sizeof(IV)*6);
            for(i=0;i<6;i++)args[i]=(n->sc.args[i])?lower_e(l,n->sc.args[i]):ivci(0,TI64);
            IV num=lower_e(l,n->sc.num);
            dst=ivreg(b,TI64);ins=ir_e(b);ins->op=IO_SYSCALL;ins->dst=dst;
            ins->s1=num;ins->na=6;ins->args=args;return dst;}
        default:return ivnone();
    }
}
static void lower_s(IRL*l,Node*n){
    IRB*b=l->b;II*ins;if(!n)return;
    switch(n->k){
        case AN_BLOCK:{int i;IScp*old=l->sc;l->sc=iscpnew(b->a,old);
            for(i=0;i<n->blk.n;i++)lower_s(l,n->blk.s[i]);l->sc=old;return;}
        case AN_VDECL:{IV addr=ivreg(b,tptr(n->vd.type));
            ins=ir_e(b);ins->op=IO_ALLOCA;ins->dst=addr;ins->atype=n->vd.type;
            iscpset(l->sc,n->vd.name,addr);
            if(n->vd.init){IV iv=lower_e(l,n->vd.init);II*st=ir_e(b);st->op=IO_STORE;st->s1=addr;st->s2=iv;}return;}
        case AN_XSTMT:lower_e(l,n->uop.op);return;
        case AN_PV:case AN_PX:{IV v=lower_e(l,n->uop.op);Type*t=v.type?v.type:TI64;
            ins=ir_e(b);
            if(t->k==TY_PTR&&t->base&&t->base->k==TY_CHAR)ins->op=IO_PSTR;
            else if(t->k==TY_PTR)ins->op=IO_PINT;
            else if(tis_flt(t))ins->op=IO_PFLT;
            else if(t->k==TY_CHAR)ins->op=IO_PCHR;
            else ins->op=IO_PINT;ins->s1=v;return;}
        case AN_PS:ins=ir_e(b);ins->op=IO_PSTR;ins->s1=ivsv(n->sv);return;
        case AN_RET:{IV rv=n->ret.val?lower_e(l,n->ret.val):ivnone();ins=ir_e(b);ins->op=IO_RET;ins->s1=rv;return;}
        case AN_IF:{IV cv=lower_e(l,n->ifs.cond);char*lend=ivlbl(b,"iend"),*lnxt=ivlbl(b,"iels");int i;
            ins=ir_e(b);ins->op=IO_JZ;ins->s1=cv;ins->lbl=lnxt;
            lower_s(l,n->ifs.then);{II*j=ir_e(b);j->op=IO_JMP;j->lbl=lend;}
            for(i=0;i<n->ifs.nelf;i++){IV ecv;
                {II*lb=ir_e(b);lb->op=IO_LBL;lb->lbl=lnxt;}lnxt=ivlbl(b,"elif");
                ecv=lower_e(l,n->ifs.econd[i]);{II*jz=ir_e(b);jz->op=IO_JZ;jz->s1=ecv;jz->lbl=lnxt;}
                lower_s(l,n->ifs.eblk[i]);{II*j=ir_e(b);j->op=IO_JMP;j->lbl=lend;}}
            {II*lb=ir_e(b);lb->op=IO_LBL;lb->lbl=lnxt;}
            if(n->ifs.el)lower_s(l,n->ifs.el);{II*lb=ir_e(b);lb->op=IO_LBL;lb->lbl=lend;}return;}
        case AN_LOOP:{char*lc=ivlbl(b,"lpc"),*le=ivlbl(b,"lpe");LL ll;IV cv;
            ll.brk=le;ll.cont=lc;ll.up=l->loops;l->loops=&ll;
            {II*lb=ir_e(b);lb->op=IO_LBL;lb->lbl=lc;}cv=lower_e(l,n->lp.cond);
            ins=ir_e(b);ins->op=IO_JZ;ins->s1=cv;ins->lbl=le;lower_s(l,n->lp.body);
            {II*j=ir_e(b);j->op=IO_JMP;j->lbl=lc;}{II*lb=ir_e(b);lb->op=IO_LBL;lb->lbl=le;}
            l->loops=ll.up;return;}
        case AN_FOR:{char*lc=ivlbl(b,"frc"),*lp2=ivlbl(b,"frp"),*le=ivlbl(b,"fre");
            IScp*old=l->sc;LL ll;IV cv;
            ll.brk=le;ll.cont=lp2;ll.up=l->loops;l->loops=&ll;l->sc=iscpnew(b->a,old);
            lower_s(l,n->fr.init);{II*lb=ir_e(b);lb->op=IO_LBL;lb->lbl=lc;}
            cv=lower_e(l,n->fr.cond);ins=ir_e(b);ins->op=IO_JZ;ins->s1=cv;ins->lbl=le;
            lower_s(l,n->fr.body);{II*lb=ir_e(b);lb->op=IO_LBL;lb->lbl=lp2;}lower_e(l,n->fr.post);
            {II*j=ir_e(b);j->op=IO_JMP;j->lbl=lc;}{II*lb=ir_e(b);lb->op=IO_LBL;lb->lbl=le;}
            l->sc=old;l->loops=ll.up;return;}
        case AN_BRK:if(l->loops){ins=ir_e(b);ins->op=IO_JMP;ins->lbl=l->loops->brk;}return;
        case AN_SKP:if(l->loops){ins=ir_e(b);ins->op=IO_JMP;ins->lbl=l->loops->cont;}return;
        case AN_FN:{int i;IScp*old;II*e;
            ins=ir_e(b);ins->op=IO_FN0;ins->fn=n->fn.name;
            old=l->sc;l->sc=iscpnew(b->a,old);
            for(i=0;i<n->fn.np;i++){II*pi=ir_e(b);pi->op=IO_PARAM;pi->dst=ivreg(b,n->fn.pt[i]);pi->fidx=(u32)i;iscpset(l->sc,n->fn.pn[i],pi->dst);}
            lower_s(l,n->fn.body);{II*r=ir_e(b);r->op=IO_RET;r->s1=ivnone();}
            l->sc=old;e=ir_e(b);e->op=IO_FN1;e->fn=n->fn.name;return;}
        case AN_ST:case AN_IM:return;
        case AN_ASM:ins=ir_e(b);ins->op=IO_ASM;ins->asmcode=n->as.code;return;
        case AN_FF:{IV pv=lower_e(l,n->ff.expr);ins=ir_e(b);ins->op=IO_FREE;ins->s1=pv;return;}
        case AN_SYSCALL:lower_e(l,n);return;
        default:return;
    }
}

/* ---------- SECTION 11: x86-64 CODEGEN ---------- */
#define RX 0  /* rax */
#define RC 1  /* rcx */
#define RD 2  /* rdx */
#define RB 3  /* rbx */
#define RS 4  /* rsp */
#define RP 5  /* rbp */
#define RI 6  /* rsi */
#define RO 7  /* rdi */
#define R8 8
#define R9 9
#define R10 10
#define R11 11
#define MRM(m,r,x) (((m)<<6)|(((r)&7)<<3)|((x)&7))
typedef struct{char*name;u32 site;}Patch;
typedef struct{
    u8*buf;u32 pos,cap;
    struct{u32 off;char*lbl;u8 type;}*relocs;u32 nrel,rcap;
    struct{char*name;u32 off;}*labels;u32 nlbl,lcap;
    i32*vslots;u32 nv;i32 stk;
    struct{char*str;u32 off;}*strs;u32 nstr,scap;
    Patch*patches;u32 npatch,pcap;
    Arena*a;
}CG;
static void cg_init(CG*c,Arena*a){memset(c,0,sizeof*c);c->cap=64*1024;c->buf=malloc(c->cap);c->a=a;}
static void cgrow(CG*c,u32 n){while(c->pos+n>c->cap){c->cap*=2;c->buf=realloc(c->buf,c->cap);}}
static void e1(CG*c,u8 b){cgrow(c,1);c->buf[c->pos++]=b;}
static void e2(CG*c,u8 a,u8 b){e1(c,a);e1(c,b);}
static void e3(CG*c,u8 a,u8 b,u8 d){e1(c,a);e1(c,b);e1(c,d);}
static void e4(CG*c,u8 a,u8 b,u8 d,u8 x){e3(c,a,b,d);e1(c,x);}
static void e32(CG*c,u32 v){cgrow(c,4);c->buf[c->pos]=(u8)v;c->buf[c->pos+1]=(u8)(v>>8);c->buf[c->pos+2]=(u8)(v>>16);c->buf[c->pos+3]=(u8)(v>>24);c->pos+=4;}
static void e64(CG*c,u64 v){int i;cgrow(c,8);for(i=0;i<8;i++)c->buf[c->pos+i]=(u8)(v>>(8*i));c->pos+=8;}
static void p32(CG*c,u32 at,u32 v){c->buf[at]=(u8)v;c->buf[at+1]=(u8)(v>>8);c->buf[at+2]=(u8)(v>>16);c->buf[at+3]=(u8)(v>>24);}
static void def_lbl(CG*c,const char*n){
    if(c->nlbl>=c->lcap){c->lcap=c->lcap?c->lcap*2:64;c->labels=realloc(c->labels,c->lcap*sizeof*c->labels);}
    c->labels[c->nlbl].name=astrdup(c->a,n);c->labels[c->nlbl].off=c->pos;c->nlbl++;}
static u32 find_lbl(CG*c,const char*n){u32 i;if(!n)return~0u;
    for(i=0;i<c->nlbl;i++)if(!strcmp(c->labels[i].name,n))return c->labels[i].off;return~0u;}
static void add_reloc(CG*c,u32 off,const char*lbl){
    if(c->nrel>=c->rcap){c->rcap=c->rcap?c->rcap*2:64;c->relocs=realloc(c->relocs,c->rcap*sizeof*c->relocs);}
    c->relocs[c->nrel].off=off;c->relocs[c->nrel].lbl=astrdup(c->a,lbl);c->relocs[c->nrel].type=0;c->nrel++;}
static void add_patch(CG*c,const char*n,u32 s){
    if(c->npatch>=c->pcap){c->pcap=c->pcap?c->pcap*2:256;c->patches=realloc(c->patches,c->pcap*sizeof*c->patches);}
    c->patches[c->npatch].name=astrdup(c->a,n);c->patches[c->npatch].site=s;c->npatch++;}
static void resolve_patches(CG*c){u32 i;
    for(i=0;i<c->npatch;i++){u32 lo=find_lbl(c,c->patches[i].name);
        if(lo!=~0u)p32(c,c->patches[i].site,(u32)(lo-(c->patches[i].site+4)));
        else fprintf(stderr,"forger: unresolved '%s'\n",c->patches[i].name?c->patches[i].name:"?");}}
/* reg ops */
static void rr(CG*c,u8 op,u8 d,u8 s){u8 rex=0x48;if(d>=8)rex|=0x04;if(s>=8)rex|=0x01;e1(c,rex);e1(c,op);e1(c,MRM(3,d&7,s&7));}
static void mri64(CG*c,u8 r,u64 v){u8 rex=0x48;if(r>=8)rex|=0x01;e1(c,rex);e1(c,(u8)(0xB8|(r&7)));e64(c,v);}
static void mri32s(CG*c,u8 r,i32 v){u8 rex=0x48;if(r>=8)rex|=0x01;e1(c,rex);e1(c,0xC7);e1(c,MRM(3,0,r&7));e32(c,(u32)v);}
/* [rbp+off] ops */
static void stloc(CG*c,i32 off,u8 r){u8 rex=0x48;if(r>=8)rex|=0x04;e1(c,rex);e1(c,0x89);
    if(off>=-128&&off<=127){e1(c,MRM(1,r&7,RP));e1(c,(u8)(i8)off);}else{e1(c,MRM(2,r&7,RP));e32(c,(u32)off);}}
static void ldloc(CG*c,u8 r,i32 off){u8 rex=0x48;if(r>=8)rex|=0x04;e1(c,rex);e1(c,0x8B);
    if(off>=-128&&off<=127){e1(c,MRM(1,r&7,RP));e1(c,(u8)(i8)off);}else{e1(c,MRM(2,r&7,RP));e32(c,(u32)off);}}
static void lea_rbp(CG*c,u8 r,i32 off){u8 rex=0x48;if(r>=8)rex|=0x04;e1(c,rex);e1(c,0x8D);
    if(off>=-128&&off<=127){e1(c,MRM(1,r&7,RP));e1(c,(u8)(i8)off);}else{e1(c,MRM(2,r&7,RP));e32(c,(u32)off);}}
static void lea_rsp(CG*c,u8 r,i8 disp){u8 rex=0x48;if(r>=8)rex|=0x04;e1(c,rex);e1(c,0x8D);e1(c,MRM(1,r&7,4));e1(c,0x24);e1(c,(u8)disp);}
static void push_r(CG*c,u8 r){if(r>=8)e1(c,0x41);e1(c,(u8)(0x50|(r&7)));}
static void pop_r(CG*c,u8 r) {if(r>=8)e1(c,0x41);e1(c,(u8)(0x58|(r&7)));}
static void add_rsp(CG*c,u32 n){e3(c,0x48,0x81,0xC4);e32(c,n);}
static void sub_rsp8(CG*c,i8 n){e4(c,0x48,0x83,0xEC,(u8)n);}
static void add_rsp8(CG*c,i8 n){e4(c,0x48,0x83,0xC4,(u8)n);}
static void cg_ret(CG*c){e1(c,0xC3);}
static void syscall_op(CG*c){e2(c,0x0F,0x05);}
static void neg_r(CG*c,u8 r){u8 rex=0x48;if(r>=8)rex|=0x01;e1(c,rex);e1(c,0xF7);e1(c,(u8)(0xD8|(r&7)));}
static void inc_r(CG*c,u8 r){u8 rex=0x48;if(r>=8)rex|=0x01;e1(c,rex);e1(c,0xFF);e1(c,MRM(3,0,r&7));}
static void dec_r(CG*c,u8 r){u8 rex=0x48;if(r>=8)rex|=0x01;e1(c,rex);e1(c,0xFF);e1(c,MRM(3,1,r&7));}
static void add_ri8(CG*c,u8 r,i8 v){u8 rex=0x48;if(r>=8)rex|=0x01;e1(c,rex);e1(c,0x83);e1(c,MRM(3,0,r&7));e1(c,(u8)v);}
static void idiv_r(CG*c,u8 r){u8 rex=0x48;if(r>=8)rex|=0x01;e1(c,rex);e1(c,0xF7);e1(c,MRM(3,7,r&7));}
static void cqo(CG*c){e2(c,0x48,0x99);}
static void setcc(CG*c,u8 cc){e3(c,0x0F,cc,0xC0);}
static void movzx_al(CG*c){e4(c,0x48,0x0F,0xB6,0xC0);}
static void store_ptr(CG*c,u8 ptr,u8 val,u32 sz){
    if(sz==1){u8 rex=0x40;if(val>=8)rex|=0x04;if(ptr>=8)rex|=0x01;e1(c,rex);e1(c,0x88);e1(c,MRM(0,val&7,ptr&7));}
    else if(sz<=4){u8 rex=0;if(val>=8)rex|=0x04;if(ptr>=8)rex|=0x01;if(rex)e1(c,rex|0x40);e1(c,0x89);e1(c,MRM(0,val&7,ptr&7));}
    else{u8 rex=0x48;if(val>=8)rex|=0x04;if(ptr>=8)rex|=0x01;e1(c,rex);e1(c,0x89);e1(c,MRM(0,val&7,ptr&7));}}
static void load_ptr(CG*c,u8 dst,u8 ptr,u32 sz){
    if(sz==1||sz==2){u8 rex=0;if(dst>=8)rex|=0x04;if(ptr>=8)rex|=0x01;if(rex)e1(c,rex|0x40);e2(c,0x0F,(sz==1)?0xB6:0xB7);e1(c,MRM(0,dst&7,ptr&7));}
    else if(sz<=4){u8 rex=0;if(dst>=8)rex|=0x04;if(ptr>=8)rex|=0x01;if(rex)e1(c,rex|0x40);e1(c,0x8B);e1(c,MRM(0,dst&7,ptr&7));}
    else{u8 rex=0x48;if(dst>=8)rex|=0x04;if(ptr>=8)rex|=0x01;e1(c,rex);e1(c,0x8B);e1(c,MRM(0,dst&7,ptr&7));}}
static void store_byte_imm(CG*c,u8 ptr,u8 imm){if(ptr>=8)e1(c,0x41);e1(c,0xC6);e1(c,MRM(0,0,ptr&7));e1(c,imm);}
static void jmp_lbl(CG*c,const char*n){u32 lo=find_lbl(c,n);e1(c,0xE9);
    if(lo!=~0u)e32(c,(u32)(lo-(c->pos+4)));else{add_patch(c,n,c->pos);e32(c,0);}}
static void jcc_lbl(CG*c,u8 cc,const char*n){u32 lo=find_lbl(c,n);e2(c,0x0F,cc);
    if(lo!=~0u)e32(c,(u32)(lo-(c->pos+4)));else{add_patch(c,n,c->pos);e32(c,0);}}
static void call_lbl(CG*c,const char*n){u32 lo=find_lbl(c,n);e1(c,0xE8);
    if(lo!=~0u)e32(c,(u32)(lo-(c->pos+4)));else{add_patch(c,n,c->pos);e32(c,0);}}
static void vres(CG*c,u32 v){if(v>=c->nv){u32 nc=v+64,i;c->vslots=realloc(c->vslots,sizeof(i32)*nc);for(i=c->nv;i<nc;i++)c->vslots[i]=0;c->nv=nc;}}
static i32 vslot(CG*c,u32 v){vres(c,v);if(!c->vslots[v]){c->stk-=8;c->vslots[v]=c->stk;}return c->vslots[v];}
static void ldv(CG*c,u8 phys,IV v){
    switch(v.k){case IV_CINT:mri64(c,phys,(u64)v.iv);break;
        case IV_CFLT:{union{double d;u64 u;}uu;uu.d=v.fv;mri64(c,phys,uu.u);break;}
        case IV_REG:ldloc(c,phys,vslot(c,v.reg));break;
        default:rr(c,0x33,phys,phys);break;}}  /* xor phys,phys */
static void stv(CG*c,IV dst,u8 phys){if(dst.k!=IV_REG)return;stloc(c,vslot(c,dst.reg),phys);}
static u32 addstr(CG*c,const char*s){u32 i;for(i=0;i<c->nstr;i++)if(!strcmp(c->strs[i].str,s))return i;
    if(c->nstr>=c->scap){c->scap=c->scap?c->scap*2:16;c->strs=realloc(c->strs,c->scap*sizeof*c->strs);}
    c->strs[c->nstr].str=astrdup(c->a,s);c->strs[c->nstr].off=0;return c->nstr++;}
static void do_alloca(CG*c,IV dst,u32 sz,bool8 init,u8 reg){
    i32 slot,aslot;if(sz<1)sz=1;sz=(sz+7)&~7u;
    c->stk-=(i32)sz;slot=c->stk;if(init)stloc(c,slot,reg);
    lea_rbp(c,RX,slot);c->stk-=8;aslot=c->stk;
    vres(c,dst.reg);c->vslots[dst.reg]=aslot;stloc(c,aslot,RX);}

/* Runtime helpers - no libc, pure syscalls */
static void emit_runtime(CG*c){
    /* _forge_pstr0(rdi=char*) */
    def_lbl(c,"_forge_pstr0");
    push_r(c,RP);e3(c,0x48,0x89,0xE5);push_r(c,RB);
    rr(c,0x8B,RB,RO); /* mov rbx,rdi */
    rr(c,0x33,RC,RC); /* xor rcx,rcx */
    {u32 loop=c->pos,jz;
     e4(c,0x0F,0xB6,0x04,0x0B); /* movzx eax,byte[rbx+rcx] */
     e2(c,0x84,0xC0);            /* test al,al */
     e1(c,0x74);jz=c->pos;e1(c,0);
     e3(c,0x48,0xFF,0xC1);       /* inc rcx */
     e1(c,0xEB);e1(c,(u8)(i8)(loop-(c->pos+1))); /* FIX 2: corrected jump offset */
     c->buf[jz]=(u8)(c->pos-(jz+1));}
    rr(c,0x8B,RI,RB);  /* mov rsi,rbx */
    rr(c,0x8B,RD,RC);  /* mov rdx,rcx */
    mri32s(c,RO,1);mri32s(c,RX,1);syscall_op(c);
    e2(c,0x6A,0x0A);            /* push 10 (\n) */
    e4(c,0x48,0x8D,0x34,0x24); /* lea rsi,[rsp] */
    mri32s(c,RO,1);mri32s(c,RD,1);mri32s(c,RX,1);syscall_op(c);
    add_rsp8(c,8);pop_r(c,RB);pop_r(c,RP);cg_ret(c);

    /* _forge_pint(rdi=i64) — signed decimal */
    def_lbl(c,"_forge_pint");
    push_r(c,RP);e3(c,0x48,0x89,0xE5);push_r(c,RB);sub_rsp8(c,32);
    rr(c,0x8B,RB,RO);  /* mov rbx,rdi (save sign) */
    rr(c,0x8B,RX,RB);  /* mov rax,rbx */
    /* negate if neg */
    rr(c,0x85,RX,RX);  /* test rax,rax (wrong: should be 64-bit) */
    /* use: 48 85 C0 = test rax,rax */
    c->pos-=3; /* undo the rr test which was 32-bit */
    e3(c,0x48,0x85,0xC0); /* test rax,rax 64-bit */
    e2(c,0x0F,0x89);{u32 s=c->pos;e32(c,0); /* jns */
        neg_r(c,RX);p32(c,s,c->pos-(s+4));}
    /* r10 = ptr into buf (rsp+31, working backwards) */
    lea_rsp(c,R10,31);
    store_byte_imm(c,R10,0); /* null-terminate */
    dec_r(c,R10);
    mri32s(c,RC,10);
    {u32 dloop=c->pos;
     rr(c,0x33,RD,RD);  /* xor rdx,rdx */
     /* but we need 64-bit xor rdx,rdx */
     c->pos-=3;e3(c,0x48,0x31,0xD2); /* xor rdx,rdx */
     idiv_r(c,RC);          /* idiv rcx: rax=quot, rdx=rem (0-9) */
     add_ri8(c,RD,48);      /* rdx += '0' */
     /* mov byte [r10], dl:  41 88 12 */
     e3(c,0x41,0x88,0x12);
     dec_r(c,R10);
     /* test rax,rax */
     e3(c,0x48,0x85,0xC0);
     e2(c,0x0F,0x85);e32(c,(u32)(i32)(dloop-(c->pos+4)));}
    /* if negative, prepend '-' */
    e3(c,0x48,0x85,0xDB); /* test rbx,rbx */
    e2(c,0x0F,0x89);{u32 s=c->pos;e32(c,0); /* jns */
        dec_r(c,R10);
        /* mov byte [r10], '-':  41 C6 02 2D */
        e4(c,0x41,0xC6,0x02,0x2D);
        p32(c,s,c->pos-(s+4));}
    /* r10 now points to first char; length = (rsp+31) - r10 */
    inc_r(c,R10);
    lea_rsp(c,RD,31);
    /* sub rdx, r10 */
    {u8 rex=0x4C;e1(c,rex);e1(c,0x29);e1(c,MRM(3,R10&7,RD&7));}
    rr(c,0x8B,RI,R10); /* mov rsi,r10 -- wrong, need 64-bit mov rsi,r10 */
    c->pos-=3;
    /* mov rsi, r10: REX.RB=0x4D, 0x89, ModRM(3,r10&7,rsi&7) -- actually 49 8B F2 = mov rsi,r10 */
    e3(c,0x4D,0x8B,0xF2); /* mov r14,r10 -- no, let me be explicit */
    /* Simpler: use a push/pop approach */
    c->pos-=3;
    /* push r10; pop rsi */
    e2(c,0x41,0x52); /* push r10 */
    pop_r(c,RI);      /* pop rsi */
    mri32s(c,RO,1);mri32s(c,RX,1);syscall_op(c);
    /* newline */
    e4(c,0xC6,0x04,0x24,0x0A); /* mov byte[rsp],'\n' */
    e4(c,0x48,0x8D,0x34,0x24); /* lea rsi,[rsp] */
    mri32s(c,RO,1);mri32s(c,RD,1);mri32s(c,RX,1);syscall_op(c);
    add_rsp8(c,32);pop_r(c,RB);pop_r(c,RP);cg_ret(c);

    /* _forge_pchr(rdi=char) */
    def_lbl(c,"_forge_pchr");
    push_r(c,RP);e3(c,0x48,0x89,0xE5);
    push_r(c,RO); /* push char onto stack */
    e3(c,0x48,0x89,0xE6); /* mov rsi,rsp */
    mri32s(c,RD,1);mri32s(c,RO,1);mri32s(c,RX,1);syscall_op(c);
    add_rsp8(c,8);pop_r(c,RP);cg_ret(c);
}

static void codegen(CG*c,IRB*b){
    u32 i;u32 fph=0;
    static const u8 arg_regs[6]={RO,RI,RD,RC,R8,R9};
    for(i=0;i<b->n;i++){
        II*ins=&b->ii[i];
        switch(ins->op){
            case IO_NOP:break;
            case IO_LBL:def_lbl(c,ins->lbl);break;
            case IO_FN0:{u32 j;def_lbl(c,ins->fn);push_r(c,RP);e3(c,0x48,0x89,0xE5);
                e3(c,0x48,0x81,0xEC);fph=c->pos;e32(c,0x200);c->stk=0;
                for(j=0;j<c->nv;j++)c->vslots[j]=0;break;}
            case IO_FN1:{u32 fs=(u32)(-c->stk);fs=(fs+15)&~15u;if(fs<16)fs=16;p32(c,fph,fs);
                rr(c,0x33,RX,RX);e3(c,0x48,0x89,0xEC);pop_r(c,RP);cg_ret(c);break;}
            case IO_PARAM:if(ins->fidx<6&&ins->dst.k==IV_REG)do_alloca(c,ins->dst,8,1,arg_regs[ins->fidx]);break;
            case IO_ALLOCA:if(ins->dst.k==IV_REG)do_alloca(c,ins->dst,ins->atype?tsz(ins->atype):8,0,0);break;
            case IO_STR:{u32 si=addstr(c,ins->s1.sv?ins->s1.sv:"");char lbl[32];
                e3(c,0x48,0x8D,0x05);sprintf(lbl,"__s%u",si);add_reloc(c,c->pos,lbl);e32(c,0);
                stv(c,ins->dst,RX);break;}
            case IO_STORE:{u32 sz=8;if(ins->s2.type){u32 bs=tsz(ins->s2.type);if(bs)sz=bs;}
                ldv(c,RX,ins->s1);ldv(c,RC,ins->s2);store_ptr(c,RX,RC,sz);break;}
            case IO_DEREF:{u32 sz=8;if(ins->dst.type){u32 bs=tsz(ins->dst.type);if(bs)sz=bs;}
                ldv(c,RX,ins->s1);load_ptr(c,RC,RX,sz);stv(c,ins->dst,RC);break;}
            case IO_ADDR:ldv(c,RX,ins->s1);stv(c,ins->dst,RX);break;
            case IO_LOAD:rr(c,0x33,RX,RX);stv(c,ins->dst,RX);break;
            case IO_ADD:case IO_SUB:case IO_AND:case IO_OR:case IO_XOR:
                ldv(c,RX,ins->s1);ldv(c,RC,ins->s2);
                switch(ins->op){case IO_ADD:rr(c,0x03,RX,RC);break;case IO_SUB:rr(c,0x2B,RX,RC);break;
                    case IO_AND:rr(c,0x23,RX,RC);break;case IO_OR:rr(c,0x0B,RX,RC);break;
                    default:rr(c,0x33,RX,RC);break;}stv(c,ins->dst,RX);break;
            case IO_MUL:ldv(c,RX,ins->s1);ldv(c,RC,ins->s2);
                e4(c,0x48,0x0F,0xAF,MRM(3,RX,RC));stv(c,ins->dst,RX);break;
            case IO_DIV:case IO_MOD:ldv(c,RX,ins->s1);ldv(c,RC,ins->s2);cqo(c);idiv_r(c,RC);
                stv(c,ins->dst,(ins->op==IO_DIV)?RX:RD);break;
            case IO_NEG:ldv(c,RX,ins->s1);neg_r(c,RX);stv(c,ins->dst,RX);break;
            case IO_NOT:ldv(c,RX,ins->s1);e3(c,0x48,0x85,0xC0);setcc(c,0x94);movzx_al(c);stv(c,ins->dst,RX);break;
            case IO_SHL:case IO_SHR:ldv(c,RX,ins->s1);ldv(c,RC,ins->s2);
                e2(c,0x48,0xD3);e1(c,(u8)(ins->op==IO_SHL?0xE0:0xE8));stv(c,ins->dst,RX);break;
            case IO_EQ:case IO_NEQ:case IO_LT:case IO_GT:case IO_LTE:case IO_GTE:{u8 cc;
                ldv(c,RX,ins->s1);ldv(c,RC,ins->s2);rr(c,0x3B,RX,RC);
                switch(ins->op){case IO_EQ:cc=0x94;break;case IO_NEQ:cc=0x95;break;
                    case IO_LT:cc=0x9C;break;case IO_GT:cc=0x9F;break;
                    case IO_LTE:cc=0x9E;break;default:cc=0x9D;break;}
                setcc(c,cc);movzx_al(c);stv(c,ins->dst,RX);break;}
            case IO_LAND:ldv(c,RX,ins->s1);ldv(c,RC,ins->s2);
                e3(c,0x48,0x85,0xC0);e3(c,0x0F,0x95,0xC0);
                e3(c,0x48,0x85,0xC9);e3(c,0x0F,0x95,0xC1);
                rr(c,0x23,RX,RC);movzx_al(c);stv(c,ins->dst,RX);break;
            case IO_LOR:ldv(c,RX,ins->s1);ldv(c,RC,ins->s2);rr(c,0x0B,RX,RC);
                e3(c,0x48,0x85,0xC0);setcc(c,0x95);movzx_al(c);stv(c,ins->dst,RX);break;
            case IO_JMP:jmp_lbl(c,ins->lbl);break;
            case IO_JZ: ldv(c,RX,ins->s1);e3(c,0x48,0x85,0xC0);jcc_lbl(c,0x84,ins->lbl);break;
            case IO_JNZ:ldv(c,RX,ins->s1);e3(c,0x48,0x85,0xC0);jcc_lbl(c,0x85,ins->lbl);break;
            case IO_CALL:{int ai,sa=ins->na>6?ins->na-6:0;u32 adj=(sa&1)?8:0;
                for(ai=0;ai<ins->na&&ai<6;ai++)ldv(c,arg_regs[ai],ins->args[ai]);
                for(ai=ins->na-1;ai>=6;ai--){ldv(c,RX,ins->args[ai]);push_r(c,RX);}
                if(adj)sub_rsp8(c,8);call_lbl(c,ins->fn?ins->fn:"");
                if(adj)add_rsp8(c,8);if(sa)add_rsp(c,(u32)sa*8);
                if(ins->dst.k==IV_REG)stv(c,ins->dst,RX);break;}
            case IO_RET:if(ins->s1.k!=IV_NONE)ldv(c,RX,ins->s1);else rr(c,0x33,RX,RX);
                e3(c,0x48,0x89,0xEC);pop_r(c,RP);cg_ret(c);break;
            case IO_MALLOC:ldv(c,RI,ins->s1);rr(c,0x33,RO,RO);mri32s(c,RD,3);mri32s(c,R10,0x22);
                mri64(c,R8,(u64)-1);rr(c,0x33,R9,R9);mri32s(c,RX,9);syscall_op(c);
                if(ins->dst.k==IV_REG)stv(c,ins->dst,RX);break;
            case IO_FREE:ldv(c,RO,ins->s1);mri32s(c,RI,4096);mri32s(c,RX,11);syscall_op(c);break;
            case IO_CAST:{bool8 df=tis_flt(ins->ctype),sf=(ins->s1.type&&tis_flt(ins->s1.type))||ins->s1.k==IV_CFLT;
                if(df&&!sf&&ins->s1.k!=IV_CFLT){i32 sl;ldv(c,RX,ins->s1);
                    e3(c,0xF2,0x48,0x0F);e2(c,0x2A,MRM(3,0,RX));sl=vslot(c,ins->dst.reg);
                    e3(c,0xF2,0x0F,0x11);if(sl>=-128&&sl<=127){e1(c,MRM(1,0,RP));e1(c,(u8)(i8)sl);}else{e1(c,MRM(2,0,RP));e32(c,(u32)sl);}
                }else if(!df&&sf&&ins->s1.k==IV_REG){i32 sl=vslot(c,ins->s1.reg);
                    e3(c,0xF2,0x0F,0x10);if(sl>=-128&&sl<=127){e1(c,MRM(1,0,RP));e1(c,(u8)(i8)sl);}else{e1(c,MRM(2,0,RP));e32(c,(u32)sl);}
                    e3(c,0xF2,0x48,0x0F);e2(c,0x2C,0xC0);stv(c,ins->dst,RX);
                }else{ldv(c,RX,ins->s1);stv(c,ins->dst,RX);}break;}
            case IO_FLD:ldv(c,RX,ins->s1);if(ins->fidx){e2(c,0x48,0x05);e32(c,ins->fidx);}stv(c,ins->dst,RX);break;
            case IO_PINT:ldv(c,RO,ins->s1);call_lbl(c,"_forge_pint");break;
            case IO_PCHR:ldv(c,RO,ins->s1);call_lbl(c,"_forge_pchr");break;
            case IO_PSTR:
                if(ins->s1.k==IV_STR){u32 si=addstr(c,ins->s1.sv?ins->s1.sv:"");char lbl[32];
                    sprintf(lbl,"__s%u",si);e3(c,0x48,0x8D,0x3D);add_reloc(c,c->pos,lbl);e32(c,0);}
                else ldv(c,RO,ins->s1);
                call_lbl(c,"_forge_pstr0");break;
            case IO_PFLT:
                if(ins->s1.k==IV_CFLT){mri64(c,RO,(u64)(i64)ins->s1.fv);call_lbl(c,"_forge_pint");}
                else if(ins->s1.k==IV_REG){i32 sl=vslot(c,ins->s1.reg);
                    e3(c,0xF2,0x0F,0x10);if(sl>=-128&&sl<=127){e1(c,MRM(1,0,RP));e1(c,(u8)(i8)sl);}else{e1(c,MRM(2,0,RP));e32(c,(u32)sl);}
                    e3(c,0xF2,0x48,0x0F);e2(c,0x2C,0xC0);rr(c,0x8B,RO,RX);call_lbl(c,"_forge_pint");}break;
            case IO_ASM:e1(c,0x90);break;
            case IO_SYSCALL:{
                /* Load syscall args: rax=num, rdi=a0, rsi=a1, rdx=a2, r10=a3, r8=a4, r9=a5 */
                static const u8 sc_regs[6]={RO,RI,RD,R10,R8,R9};
                int ai;
                /* load args first (may clobber rax) */
                for(ai=5;ai>=0;ai--)if(ins->args[ai].k!=IV_NONE)ldv(c,sc_regs[ai],ins->args[ai]);
                ldv(c,RX,ins->s1); /* syscall number -> rax */
                syscall_op(c);
                if(ins->dst.k==IV_REG)stv(c,ins->dst,RX);break;}
            default:break;
        }
    }
}

static void emit_entry(CG*c){
    def_lbl(c,"_start");
    call_lbl(c,"main");
    e3(c,0x48,0x89,0xC7); /* mov rdi,rax — pass return value as exit code */
    mri32s(c,RX,60);       /* sys_exit */
    syscall_op(c);
}
static void finalize_strings(CG*c){
    u32 i,off=c->pos;
    for(i=0;i<c->nstr;i++){c->strs[i].off=off;off+=(u32)strlen(c->strs[i].str)+1;}
    for(i=0;i<c->nrel;i++){
        if(!strncmp(c->relocs[i].lbl,"__s",3)){
            u32 n=(u32)atoi(c->relocs[i].lbl+3);
            if(n<c->nstr){i32 rel=(i32)(c->strs[n].off-(c->relocs[i].off+4));p32(c,c->relocs[i].off,(u32)rel);}
        }
    }
}
static u32 strpool_sz(CG*c){u32 i,s=0;for(i=0;i<c->nstr;i++)s+=(u32)strlen(c->strs[i].str)+1;return s;}
static void copy_strs(u8*dst,CG*c){u32 i,o=0;for(i=0;i<c->nstr;i++){u32 sl=(u32)strlen(c->strs[i].str)+1;memcpy(dst+o,c->strs[i].str,sl);o+=sl;}}

/* ---------- SECTION 12: EMITTERS ---------- */
static void wle16(u8*p,u16 v){p[0]=(u8)v;p[1]=(u8)(v>>8);}
static void wle32(u8*p,u32 v){p[0]=(u8)v;p[1]=(u8)(v>>8);p[2]=(u8)(v>>16);p[3]=(u8)(v>>24);}
static void wle64(u8*p,u64 v){int i;for(i=0;i<8;i++)p[i]=(u8)(v>>(8*i));}
static void chmod_x(const char*path){
#if !PLATFORM_WINDOWS
    char cmd[512];int r;sprintf(cmd,"chmod +x \"%s\"",path);r=system(cmd);(void)r;
#else
    (void)path; /* FIX 1: corrected preprocessor directive */
#endif
}

static void emit_elf64(const char*path,CG*c,u32 eoff){
    u64 load=0x400000;u32 hdr=120,pool=strpool_sz(c),fsz=hdr+c->pos+pool;
    u8*f=(u8*)calloc(fsz+16,1);u8*ph;
    f[0]=0x7F;f[1]='E';f[2]='L';f[3]='F';f[4]=2;f[5]=1;f[6]=1;
    wle16(f+16,2);wle16(f+18,0x3E);wle32(f+20,1);
    wle64(f+24,load+hdr+eoff);wle64(f+32,64);
    wle16(f+52,64);wle16(f+54,56);wle16(f+56,1);wle16(f+58,64);
    ph=f+64;wle32(ph,1);wle32(ph+4,5);wle64(ph+8,0);wle64(ph+16,load);wle64(ph+24,load);
    wle64(ph+32,fsz);wle64(ph+40,fsz);wle64(ph+48,0x200000);
    memcpy(f+hdr,c->buf,c->pos);copy_strs(f+hdr+c->pos,c);
    {FILE*fp=fopen(path,"wb");if(!fp){fprintf(stderr,"forger: cannot write '%s'\n",path);exit(1);}
     fwrite(f,1,fsz,fp);fclose(fp);free(f);}
    chmod_x(path);printf("forger: ELF64  %s  (%u bytes)\n",path,fsz);
}
static void emit_pe32plus(const char*path,CG*c,u32 eoff){
    u32 fa=0x400,pool=strpool_sz(c),total=c->pos+pool,raw=(total+fa-1)&~(fa-1),hdr=0x400,fsz=hdr+raw;
    u8*f=(u8*)calloc(fsz+16,1);u8*pe,*opt,*sec;
    f[0]='M';f[1]='Z';wle32(f+0x3C,0x80);
    {const char*m="This program cannot be run in DOS mode.\r\n$";memcpy(f+0x40,m,strlen(m));}
    pe=f+0x80;pe[0]='P';pe[1]='E';wle16(pe+4,0x8664);wle16(pe+6,1);wle16(pe+20,0xF0);wle16(pe+22,0x0022);
    opt=pe+24;wle16(opt,0x020B);wle32(opt+4,raw);wle32(opt+16,hdr+eoff);wle32(opt+20,hdr);
    wle64(opt+24,0x140000000ULL);wle32(opt+32,fa);wle32(opt+36,fa);wle16(opt+40,6);wle16(opt+48,6);
    wle32(opt+56,(fsz+fa-1)&~(fa-1));wle32(opt+60,hdr);wle16(opt+68,3);wle16(opt+70,0x8160);
    wle64(opt+72,0x100000);wle64(opt+80,0x1000);wle64(opt+88,0x100000);wle64(opt+96,0x1000);wle32(opt+108,16);
    sec=opt+0xF0;memcpy(sec,".text\0\0\0",8);wle32(sec+8,total);wle32(sec+12,hdr);wle32(sec+16,raw);wle32(sec+20,hdr);wle32(sec+36,0xE0000020);
    memcpy(f+hdr,c->buf,c->pos);copy_strs(f+hdr+c->pos,c);
    {FILE*fp=fopen(path,"wb");if(!fp){fprintf(stderr,"forger: cannot write '%s'\n",path);exit(1);}
     fwrite(f,1,fsz,fp);fclose(fp);free(f);}
    printf("forger: PE32+  %s  (%u bytes)\n",path,fsz);
}
static void emit_flat(const char*path,CG*c){
    FILE*fp=fopen(path,"wb");u32 pool=strpool_sz(c);
    if(!fp){fprintf(stderr,"forger: cannot write '%s'\n",path);exit(1);}
    fwrite(c->buf,1,c->pos,fp);{u32 i;for(i=0;i<c->nstr;i++)fwrite(c->strs[i].str,1,strlen(c->strs[i].str)+1,fp);}
    fclose(fp);printf("forger: flat   %s  (%u bytes)\n",path,c->pos+pool);
}
static void emit_macho(const char*path,CG*c,u32 eoff){
    u32 page=0x1000,scsz=72+80,tcsz=16+42*8;
    u32 hdr=(32+scsz+tcsz+page-1)&~(page-1);
    u32 pool=strpool_sz(c),csz=c->pos+pool,fsz=hdr+csz;
    u64 vm=0x100000000ULL;u8*f=(u8*)calloc(fsz+16,1);u8*lc,*sc,*tc;
    wle32(f,0xFEEDFACFu);wle32(f+4,0x01000007u);wle32(f+8,3);wle32(f+12,2);wle32(f+16,2);wle32(f+20,scsz+tcsz);
    lc=f+32;wle32(lc,0x19);wle32(lc+4,scsz);memcpy(lc+8,"__TEXT\0\0\0\0\0\0\0\0\0\0",16);
    wle64(lc+24,vm);wle64(lc+32,fsz);wle64(lc+40,0);wle64(lc+48,fsz);wle32(lc+56,7);wle32(lc+60,5);wle32(lc+64,1);
    sc=lc+72;memcpy(sc,"__text\0\0\0\0\0\0\0\0\0\0",16);memcpy(sc+16,"__TEXT\0\0\0\0\0\0\0\0\0\0",16);
    wle64(sc+32,vm+hdr);wle64(sc+40,csz);wle32(sc+48,hdr);wle32(sc+52,4);wle32(sc+64,0x80000400);
    tc=lc+scsz;wle32(tc,0x05);wle32(tc+4,tcsz);wle32(tc+8,4);wle32(tc+12,42);wle64(tc+16+16*8,vm+hdr+eoff);
    memcpy(f+hdr,c->buf,c->pos);copy_strs(f+hdr+c->pos,c);
    {FILE*fp=fopen(path,"wb");if(!fp){fprintf(stderr,"forger: cannot write '%s'\n",path);exit(1);}
     fwrite(f,1,fsz,fp);fclose(fp);free(f);}
    chmod_x(path);printf("forger: Mach-O %s  (%u bytes)\n",path,fsz);
}

/* ---------- SECTION 13: FGL CUSTOM EMITTER ---------- */
#define FGL_MAX (16<<20)
typedef struct{u8*buf;u32 pos,cap,coff;bool8 cp;}FO;
static void fgrow(FO*o,u32 n){while(o->pos+n>o->cap){if(o->cap>=FGL_MAX){fputs("forger: fgl too large\n",stderr);exit(1);}o->cap*=2;o->buf=realloc(o->buf,o->cap);}}
static void fe8(FO*o,u8 v){fgrow(o,1);o->buf[o->pos++]=v;}
static void fle16(FO*o,u16 v){fgrow(o,2);o->buf[o->pos]=(u8)v;o->buf[o->pos+1]=(u8)(v>>8);o->pos+=2;}
static void fle32(FO*o,u32 v){fgrow(o,4);wle32(o->buf+o->pos,v);o->pos+=4;}
static void fle64(FO*o,u64 v){fgrow(o,8);wle64(o->buf+o->pos,v);o->pos+=8;}
static void fbe16(FO*o,u16 v){fgrow(o,2);o->buf[o->pos]=(u8)(v>>8);o->buf[o->pos+1]=(u8)v;o->pos+=2;}
static void fbe32(FO*o,u32 v){fgrow(o,4);o->buf[o->pos]=(u8)(v>>24);o->buf[o->pos+1]=(u8)(v>>16);o->buf[o->pos+2]=(u8)(v>>8);o->buf[o->pos+3]=(u8)v;o->pos+=4;}
static void fbe64(FO*o,u64 v){int i;fgrow(o,8);for(i=7;i>=0;i--)o->buf[o->pos+7-i]=(u8)(v>>(8*i));o->pos+=8;}
static void fp32(FO*o,u32 at,u32 v){wle32(o->buf+at,v);}
static void fp64(FO*o,u32 at,u64 v){wle64(o->buf+at,v);}
static char*ftok(char**p){
    char*s;
    while(**p==' '||**p=='\t')(*p)++;
    if(!**p||**p=='\n'||**p=='\r'||**p=='#'){*p+=strlen(*p);return 0;}
    s=*p;
    while(**p && **p!=' ' && **p!='\t' && **p!='\n' && **p!='\r')(*p)++;
    if(**p){ **p = 0; (*p)++; } /* FIX 3: null-terminate tokens properly */
    return s;
}
static void ftok_null_prev(char**p){/* ftok already null-terminated */}
static u64 fnum(const char*s){if(!s)return 0;if(s[0]=='0'&&(s[1]=='x'||s[1]=='X'))return strtoull(s+2,0,16);return strtoull(s,0,10);}
static void emit_custom(const char*path,CG*c,u32 eoff,const char*fgl){
    FILE*f=fopen(fgl,"r");char line[4096];int lno=0;FO o;
    u32 pool=strpool_sz(c),ctotal=c->pos+pool;
    if(!f){fprintf(stderr,"forger: cannot open fgl '%s'\n",fgl);exit(1);}
    o.buf=calloc(65536,1);o.pos=0;o.cap=65536;o.coff=0;o.cp=0;
    while(fgets(line,sizeof line,f)){
        char*p=line;char*cmd;lno++;
        {char*nl=strchr(line,'\n');if(nl)*nl=0;}
        /* null-terminate each token by modifying line in-place */
        cmd=ftok(&p);if(!cmd)continue;
        if(!strcmp(cmd,"MAGIC")||!strcmp(cmd,"FIELD")){
            char*type=ftok(&p);if(!type)continue;
            if(!strcmp(type,"byte")){char*bv;while((bv=ftok(&p)))fe8(&o,(u8)fnum(bv));}
            else if(!strcmp(type,"le8")) fe8(&o,(u8)fnum(ftok(&p)));
            else if(!strcmp(type,"le16"))fle16(&o,(u16)fnum(ftok(&p)));
            else if(!strcmp(type,"le32"))fle32(&o,(u32)fnum(ftok(&p)));
            else if(!strcmp(type,"le64"))fle64(&o,fnum(ftok(&p)));
            else if(!strcmp(type,"be16"))fbe16(&o,(u16)fnum(ftok(&p)));
            else if(!strcmp(type,"be32"))fbe32(&o,(u32)fnum(ftok(&p)));
            else if(!strcmp(type,"be64"))fbe64(&o,fnum(ftok(&p)));
            else if(!strcmp(type,"str")){char*sv=ftok(&p);if(sv){u32 sl=(u32)strlen(sv);fgrow(&o,sl);memcpy(o.buf+o.pos,sv,sl);o.pos+=sl;fe8(&o,0);}}
            else fprintf(stderr,"fgl:%d: unknown type '%s'\n",lno,type);
        }else if(!strcmp(cmd,"PAD")){u32 n=(u32)fnum(ftok(&p));fgrow(&o,n);memset(o.buf+o.pos,0,n);o.pos+=n;}
        else if(!strcmp(cmd,"ALIGN")){u32 n=(u32)fnum(ftok(&p));if(n>1){u32 t=(o.pos+n-1)&~(n-1);while(o.pos<t)fe8(&o,0);}}
        else if(!strcmp(cmd,"OFFSET")){u32 t=(u32)fnum(ftok(&p));if(t<o.pos)fprintf(stderr,"fgl:%d: OFFSET < pos\n",lno);else while(o.pos<t)fe8(&o,0);}
        else if(!strcmp(cmd,"CODE")){o.coff=o.pos;o.cp=1;fgrow(&o,ctotal);memcpy(o.buf+o.pos,c->buf,c->pos);copy_strs(o.buf+o.pos+c->pos,c);o.pos+=ctotal;}
        else if(!strcmp(cmd,"STRINGS")){fgrow(&o,pool);copy_strs(o.buf+o.pos,c);o.pos+=pool;}
        else if(!strcmp(cmd,"ENTRY_OFF32")){u32 fx=(u32)fnum(ftok(&p));fp32(&o,fx,eoff);}
        else if(!strcmp(cmd,"ENTRY_OFF64")){u32 fx=(u32)fnum(ftok(&p));fp64(&o,fx,(u64)eoff);}
        else if(!strcmp(cmd,"ENTRY_VA32")){u64 base=fnum(ftok(&p));u32 fx=(u32)fnum(ftok(&p));fp32(&o,fx,(u32)(base+o.coff+eoff));}
        else if(!strcmp(cmd,"ENTRY_VA64")){u64 base=fnum(ftok(&p));u32 fx=(u32)fnum(ftok(&p));fp64(&o,fx,base+o.coff+eoff);}
        else if(!strcmp(cmd,"SIZE32")){u32 fx=(u32)fnum(ftok(&p));fp32(&o,fx,o.pos);}
        else if(!strcmp(cmd,"CODESIZE32")){u32 fx=(u32)fnum(ftok(&p));fp32(&o,fx,ctotal);}
        else fprintf(stderr,"fgl:%d: unknown directive '%s'\n",lno,cmd);
    }
    fclose(f);
    {FILE*fp=fopen(path,"wb");if(!fp){fprintf(stderr,"forger: cannot write '%s'\n",path);free(o.buf);exit(1);}
     fwrite(o.buf,1,o.pos,fp);fclose(fp);free(o.buf);}
    chmod_x(path);printf("forger: custom %s  (%u bytes)  [%s]\n",path,o.pos,fgl);
}

/* ---------- SECTION 14: DRIVER ---------- */
static char*read_file(const char*path){FILE*f=fopen(path,"rb");char*buf;long sz;
    if(!f){fprintf(stderr,"forger: cannot open '%s'\n",path);exit(1);}
    fseek(f,0,SEEK_END);sz=ftell(f);fseek(f,0,SEEK_SET);buf=malloc(sz+1);
    if(fread(buf,1,sz,f)!=(size_t)sz){fprintf(stderr,"forger: read error\n");exit(1);}
    fclose(f);buf[sz]=0;return buf;}

static void usage(void){
    puts("Forger - The Forge Language Compiler");
    puts("Usage: forger <source.fg> [options]");
    puts("  -o <file>     output (default: out)");
    puts("  -t <fmt>      elf64|pe32|flat|macho|custom  (default: elf64)");
    puts("  -i <f.fgl>    layout file for -t custom  (also: -i:/path/to/file.fgl)");
    puts("  -v            verbose / dump IR");
    puts("  -h            help");
    puts("");
    puts("Forge syntax:");
    puts("  V i32 x = 5         variable");
    puts("  PV x                print variable");
    puts("  PS \"hello\"          print string literal");
    puts("  P expr              print expression");
    puts("  FN f(i32 a) i32 { RT a+1 }");
    puts("  EX FN main() i32 { RT 0 }");
    puts("  IF x>0 { } ELF x==0 { } EL { }");
    puts("  LP x<10 { x++ }     while loop");
    puts("  FR V i32 i=0; i<10; i++ { }");
    puts("  BK / SK             break / continue");
    puts("  AL i32 16           alloc heap (returns pointer)");
    puts("  FF ptr              free");
    puts("  DR ptr              dereference");
    puts("  CT(i32,expr)        cast");
    puts("  SZ(i32)             sizeof");
    puts("  ST Point{i32 x;i32 y}  struct");
    puts("  ASM{nop}            inline asm (NOP stub)");
    puts("  SC(num,a,b,c,d,e,f) native syscall — returns i64");
    puts("    e.g. SC(60,0,0,0,0,0,0)  = sys_exit(0)");
    puts("         SC(1,1,ptr,len,0,0,0) = sys_write(stdout,ptr,len)");
    puts("  Types: vd bl i8 i16 i32 i64 u8 u16 u32 u64 f32 f64 ch str pt");
}

int main(int argc,char**argv){
    const char*src_path=0,*out_path="out",*target="elf64",*fgl_path=0;
    int i;char*src;Arena la,sa,ia,ca;Lexer lx;Par par;Node*prog;
    SymTab syms;Sem sem;IRB irb;IRL lower;CG ctx;u32 eoff;

    if(argc<2){usage();return 0;}
    for(i=1;i<argc;i++){
        if(!strcmp(argv[i],"-h")){usage();return 0;}
        else if(!strcmp(argv[i],"-v"))g_verbose=1;
        else if(!strcmp(argv[i],"-o")&&i+1<argc)out_path=argv[++i];
        else if(!strcmp(argv[i],"-t")&&i+1<argc)target=argv[++i];
        else if(!strcmp(argv[i],"-i")&&i+1<argc)fgl_path=argv[++i];
        else if(!strncmp(argv[i],"-i:",3))fgl_path=argv[i]+3;
        else if(!strcmp(argv[i],"-O0")||!strcmp(argv[i],"-O1")||!strcmp(argv[i],"-O2")){}
        else if(argv[i][0]!='-')src_path=argv[i];
        else{fprintf(stderr,"forger: unknown option '%s'\n",argv[i]);return 1;}
    }
    if(!src_path){fputs("forger: no input file\n",stderr);return 1;}
    if(!strcmp(target,"custom")&&!fgl_path){fputs("forger: -t custom requires -i <layout.fgl>\n",stderr);return 1;}
    g_src=src_path;src=read_file(src_path);types_init();

    /* Lex */
    arena_init(&la);memset(&lx,0,sizeof lx);
    lx.src=src;lx.len=(u32)strlen(src);lx.ln=1;lx.cl=1;lx.arena=&la;
    lexer_lex(&lx);if(g_verbose)printf("forger: %u tokens\n",lx.ntok);

    /* Parse */
    arena_init(&g_ast);par.t=lx.toks;par.n=lx.ntok;par.pos=0;par.a=&g_ast;
    prog=pprog(&par);if(g_errs){fprintf(stderr,"forger: %d parse error(s)\n",g_errs);return 1;}

    /* Semantic */
    arena_init(&sa);st_init(&syms,&sa);st_push(&syms);
    sem.s=&syms;sem.a=&sa;sem.fnret=0;sem.ldepth=0;
    for(i=0;i<prog->blk.n;i++)sem_s(&sem,prog->blk.s[i]);
    if(g_errs){fprintf(stderr,"forger: %d semantic error(s)\n",g_errs);return 1;}

    /* IR */
    arena_init(&ia);ir_init(&irb,&ia);
    lower.b=&irb;lower.a=&ia;lower.sc=iscpnew(&ia,0);lower.loops=0;
    for(i=0;i<prog->blk.n;i++){Node*s=prog->blk.s[i];
        if(s->k==AN_FN||s->k==AN_ST||s->k==AN_IM||s->k==AN_ASM)lower_s(&lower,s);
        else WARN(s->ln,s->cl,"top-level code outside functions ignored");}

    /* Codegen */
    arena_init(&ca);cg_init(&ctx,&ca);
    emit_runtime(&ctx);
    codegen(&ctx,&irb);
    if(find_lbl(&ctx,"main")==~0u){fputs("forger: no 'main' function\n",stderr);return 1;}
    emit_entry(&ctx);
    resolve_patches(&ctx);
    finalize_strings(&ctx);
    eoff=find_lbl(&ctx,"_start");
    if(g_verbose)printf("forger: code=%u bytes  entry=0x%X\n",ctx.pos,eoff);

    /* Emit */
    if(!strcmp(target,"elf64"))      emit_elf64(out_path,&ctx,eoff);
    else if(!strcmp(target,"pe32"))  emit_pe32plus(out_path,&ctx,eoff);
    else if(!strcmp(target,"flat"))  emit_flat(out_path,&ctx);
    else if(!strcmp(target,"macho")) emit_macho(out_path,&ctx,eoff);
    else if(!strcmp(target,"custom"))emit_custom(out_path,&ctx,eoff,fgl_path);
    else{fprintf(stderr,"forger: unknown target '%s'\n",target);return 1;}

    free(src);free(lx.toks);free(ctx.buf);free(ctx.vslots);
    free(ctx.relocs);free(ctx.labels);free(ctx.strs);free(ctx.patches);
    arena_free(&la);arena_free(&g_ast);arena_free(&sa);
    arena_free(&ia);arena_free(&ca);arena_free(&g_ty_arena);
    return g_errs?1:0;
}
