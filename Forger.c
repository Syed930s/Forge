#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>

#if defined(_WIN32) || defined(_WIN64)
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
#define NULL_PTR 0

#define ARENA_BLOCK_SIZE (1024 * 1024)

typedef struct ArenaBlock {
    u8               *data;
    u32               used;
    u32               capacity;
    struct ArenaBlock *next;
} ArenaBlock;

typedef struct {
    ArenaBlock *head;
    ArenaBlock *current;
    u64         total_allocated;
} Arena;

static ArenaBlock *arena_new_block(u32 min_size) {
    ArenaBlock *blk = (ArenaBlock*)malloc(sizeof(ArenaBlock));
    u32 cap = min_size > ARENA_BLOCK_SIZE ? min_size : ARENA_BLOCK_SIZE;

    blk->data     = (u8*)malloc(cap);
    blk->used     = 0;
    blk->capacity = cap;
    blk->next     = NULL_PTR;

    return blk;
}

static void arena_init(Arena *a) {
    a->head            = arena_new_block(ARENA_BLOCK_SIZE);
    a->current         = a->head;
    a->total_allocated = 0;
}

static void *arena_alloc(Arena *a, u32 size) {
    void *ptr;
    u32 aligned = (size + 7) & ~7u;

    if (a->current->used + aligned > a->current->capacity) {
        ArenaBlock *blk  = arena_new_block(aligned);
        a->current->next = blk;
        a->current       = blk;
    }

    ptr               = a->current->data + a->current->used;
    a->current->used += aligned;
    a->total_allocated += aligned;

    memset(ptr, 0, aligned);
    return ptr;
}

static char *arena_strdup(Arena *a, const char *s) {
    u32   len = (u32)strlen(s) + 1;
    char *out = (char*)arena_alloc(a, len);
    memcpy(out, s, len);
    return out;
}

static void arena_free(Arena *a) {
    ArenaBlock *blk = a->head;

    while (blk) {
        ArenaBlock *next = blk->next;
        free(blk->data);
        free(blk);
        blk = next;
    }

    a->head = a->current = NULL_PTR;
}

typedef enum {
    SEV_WARNING,
    SEV_ERROR,
    SEV_FATAL
} Severity;

static const char *g_source_file = "";
static int g_error_count = 0;
static int g_verbose     = 0;

static void report(Severity sev, int line, int col, const char *fmt, ...) {
    va_list ap;
    const char *prefix = sev == SEV_WARNING ? "warning" :
                         sev == SEV_ERROR   ? "error"   : "fatal";

    fprintf(stderr, "%s:%d:%d: %s: ", g_source_file, line, col, prefix);

    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);

    fprintf(stderr, "\n");

    if (sev == SEV_ERROR) g_error_count++;
    if (sev == SEV_FATAL) {
        fprintf(stderr, "forger: compilation aborted\n");
        exit(1);
    }
}

#define WARN(line, col, ...)  report(SEV_WARNING, line, col, __VA_ARGS__)
#define ERROR(line, col, ...) report(SEV_ERROR,   line, col, __VA_ARGS__)
#define FATAL(line, col, ...) report(SEV_FATAL,   line, col, __VA_ARGS__)

typedef struct {
    char   ext[64];
    char   arch[64];
    u32    bits;
    char   mode[64];

    u8    *header;
    u32    header_len;
    u32    header_cap;

    u32    code_offset;
    bool8  has_code_offset;

    u32    entry_patch_offset;
    bool8  has_entry_patch;

    u32    entry_patch_width;
    u64    entry_base;
} TargetFGL;

static bool8 fgl_is_space(char c) {
    return c == ' ' || c == '\t' || c == '\r' || c == '\n';
}

static char *fgl_trim(char *s) {
    char *end;

    while (fgl_is_space(*s)) s++;

    if (*s == 0) return s;

    end = s + strlen(s) - 1;

    while (end > s && fgl_is_space(*end)) {
        *end = 0;
        end--;
    }

    if (end == s && fgl_is_space(*end)) {
        *end = 0;
    }

    return s;
}

static bool8 directive_is(const char *s, const char *kw) {
    size_t n = strlen(kw);

    if (strncmp(s, kw, n) != 0) return FALSE;

    return s[n] == 0 || fgl_is_space(s[n]);
}

static char *directive_value(char *s, const char *kw) {
    return fgl_trim(s + strlen(kw));
}

static void target_append(TargetFGL *t, const u8 *data, u32 len) {
    if (len == 0) return;

    if (t->header_len + len > t->header_cap) {
        u32 newcap = t->header_cap ? t->header_cap : 256;

        while (newcap < t->header_len + len) {
            newcap *= 2;
        }

        t->header = (u8*)realloc(t->header, newcap);
        t->header_cap = newcap;
    }

    memcpy(t->header + t->header_len, data, len);
    t->header_len += len;
}

static u8 *read_file_bytes(const char *path, u32 *out_len) {
    FILE *f = fopen(path, "rb");
    long sz;
    u8 *buf;

    if (!f) {
        fprintf(stderr, "forger: cannot open file '%s'\n", path);
        exit(1);
    }

    fseek(f, 0, SEEK_END);
    sz = ftell(f);
    fseek(f, 0, SEEK_SET);

    if (sz < 0) {
        fprintf(stderr, "forger: cannot determine size of '%s'\n", path);
        fclose(f);
        exit(1);
    }

    buf = (u8*)malloc(sz == 0 ? 1 : (size_t)sz);

    if (sz > 0 && fread(buf, 1, (size_t)sz, f) != (size_t)sz) {
        fprintf(stderr, "forger: failed reading '%s'\n", path);
        fclose(f);
        exit(1);
    }

    fclose(f);

    if (out_len) *out_len = (u32)sz;
    return buf;
}

static void target_parse_bytes(TargetFGL *t, char *p) {
    while (*p) {
        unsigned long v;
        char *end;
        u8 b;

        while (*p && (fgl_is_space(*p) || *p == ',')) {
            p++;
        }

        if (!*p) break;

        v = strtoul(p, &end, 0);

        if (end == p) {
            fprintf(stderr, "forger: bad byte value in FGL target\n");
            exit(1);
        }

        if (v > 255) {
            fprintf(stderr, "forger: byte value out of range 0..255 in FGL target\n");
            exit(1);
        }

        b = (u8)v;
        target_append(t, &b, 1);

        p = end;
    }
}

static void load_target_fgl(const char *path, TargetFGL *t) {
    FILE *f = fopen(path, "rb");
    char line[65536];
    int ln = 0;

    if (!f) {
        fprintf(stderr, "forger: cannot open FGL target '%s'\n", path);
        exit(1);
    }

    while (fgets(line, sizeof(line), f)) {
        char *s;

        ln++;
        s = fgl_trim(line);

        if (!*s || *s == '#') continue;

        if (directive_is(s, "EXT")) {
            strncpy(t->ext, directive_value(s, "EXT"), sizeof(t->ext) - 1);
            t->ext[sizeof(t->ext) - 1] = 0;
        } else if (directive_is(s, "ARCH")) {
            strncpy(t->arch, directive_value(s, "ARCH"), sizeof(t->arch) - 1);
            t->arch[sizeof(t->arch) - 1] = 0;
        } else if (directive_is(s, "BITS")) {
            t->bits = (u32)strtoul(directive_value(s, "BITS"), NULL, 0);
        } else if (directive_is(s, "MODE")) {
            strncpy(t->mode, directive_value(s, "MODE"), sizeof(t->mode) - 1);
            t->mode[sizeof(t->mode) - 1] = 0;
        } else if (directive_is(s, "MAGIC")) {
            target_parse_bytes(t, directive_value(s, "MAGIC"));
        } else if (directive_is(s, "HEADER-BYTES")) {
            target_parse_bytes(t, directive_value(s, "HEADER-BYTES"));
        } else if (directive_is(s, "HEADER-FILE")) {
            char *v = directive_value(s, "HEADER-FILE");
            u32 len = 0;
            u8 *b = read_file_bytes(v, &len);

            target_append(t, b, len);
            free(b);
        } else if (directive_is(s, "CODE-OFFSET")) {
            t->code_offset = (u32)strtoul(directive_value(s, "CODE-OFFSET"), NULL, 0);
            t->has_code_offset = TRUE;
        } else if (directive_is(s, "ENTRY-PATCH-OFFSET")) {
            t->entry_patch_offset = (u32)strtoul(directive_value(s, "ENTRY-PATCH-OFFSET"), NULL, 0);
            t->has_entry_patch = TRUE;
        } else if (directive_is(s, "ENTRY-PATCH-WIDTH")) {
            t->entry_patch_width = (u32)strtoul(directive_value(s, "ENTRY-PATCH-WIDTH"), NULL, 0);
        } else if (directive_is(s, "ENTRY-BASE")) {
            t->entry_base = (u64)strtoull(directive_value(s, "ENTRY-BASE"), NULL, 0);
        } else {
            fprintf(stderr, "forger: unknown FGL target directive near line %d in '%s'\n", ln, path);
            exit(1);
        }
    }

    fclose(f);

    if (!t->ext[0]) {
        strcpy(t->ext, "bin");
    }

    if (t->entry_patch_width != 4 && t->entry_patch_width != 8) {
        t->entry_patch_width = 8;
    }
}

typedef enum {
    TY_VOID,
    TY_BOOL,
    TY_I8, TY_I16, TY_I32, TY_I64,
    TY_U8, TY_U16, TY_U32, TY_U64,
    TY_F32, TY_F64,
    TY_CHAR,
    TY_PTR,
    TY_ARRAY,
    TY_STRUCT,
    TY_FN,
    TY_UNKNOWN
} TypeKind;

typedef struct Type Type;

typedef struct TypeField {
    char            *name;
    Type            *type;
    struct TypeField *next;
} TypeField;

struct Type {
    TypeKind  kind;
    Type     *base;
    u32       array_size;
    char     *name;
    TypeField *fields;

    Type    **param_types;
    int       param_count;
    Type     *ret_type;
};

static Arena g_type_arena;

static Type *type_new(TypeKind kind) {
    Type *t  = (Type*)arena_alloc(&g_type_arena, sizeof(Type));
    t->kind  = kind;
    return t;
}

static Type *TY_VOID_T;
static Type *TY_BOOL_T;
static Type *TY_I8_T;
static Type *TY_I16_T;
static Type *TY_I32_T;
static Type *TY_I64_T;
static Type *TY_U8_T;
static Type *TY_U16_T;
static Type *TY_U32_T;
static Type *TY_U64_T;
static Type *TY_F32_T;
static Type *TY_F64_T;
static Type *TY_CHAR_T;
static Type *TY_UNKNOWN_T;

static u32 type_align(Type *t);
static u32 type_size(Type *t);

static void types_init(void) {
    arena_init(&g_type_arena);

    TY_VOID_T  = type_new(TY_VOID);
    TY_BOOL_T  = type_new(TY_BOOL);

    TY_I8_T    = type_new(TY_I8);
    TY_I16_T   = type_new(TY_I16);
    TY_I32_T   = type_new(TY_I32);
    TY_I64_T   = type_new(TY_I64);

    TY_U8_T    = type_new(TY_U8);
    TY_U16_T   = type_new(TY_U16);
    TY_U32_T   = type_new(TY_U32);
    TY_U64_T   = type_new(TY_U64);

    TY_F32_T   = type_new(TY_F32);
    TY_F64_T   = type_new(TY_F64);

    TY_CHAR_T  = type_new(TY_CHAR);
    TY_UNKNOWN_T = type_new(TY_UNKNOWN);
}

static Type *type_ptr(Type *base) {
    Type *t = type_new(TY_PTR);
    t->base = base;
    return t;
}

static Type *type_array(Type *base, u32 size) {
    Type *t       = type_new(TY_ARRAY);
    t->base       = base;
    t->array_size = size;
    return t;
}

static u32 type_align(Type *t) {
    switch (t->kind) {
        case TY_I8: case TY_U8: case TY_BOOL: case TY_CHAR:
            return 1;

        case TY_I16: case TY_U16:
            return 2;

        case TY_I32: case TY_U32: case TY_F32:
            return 4;

        case TY_I64: case TY_U64: case TY_F64: case TY_PTR:
            return 8;

        case TY_ARRAY:
            return type_align(t->base);

        case TY_STRUCT: {
            u32 max_align = 1;
            TypeField *f = t->fields;

            while (f) {
                u32 a = type_align(f->type);
                if (a > max_align) max_align = a;
                f = f->next;
            }

            return max_align;
        }

        default:
            return 8;
    }
}

static u32 type_field_offset(Type *st, const char *field_name) {
    u32 offset = 0;
    TypeField *f = st->fields;

    while (f) {
        u32 align = type_align(f->type);

        offset = (offset + align - 1) & ~(align - 1);

        if (strcmp(f->name, field_name) == 0) {
            return offset;
        }

        offset += type_size(f->type);
        f = f->next;
    }

    return 0;
}

static u32 type_size(Type *t) {
    switch (t->kind) {
        case TY_VOID:
            return 0;

        case TY_BOOL:
        case TY_I8:
        case TY_U8:
        case TY_CHAR:
            return 1;

        case TY_I16:
        case TY_U16:
            return 2;

        case TY_I32:
        case TY_U32:
        case TY_F32:
            return 4;

        case TY_I64:
        case TY_U64:
        case TY_F64:
        case TY_PTR:
            return 8;

        case TY_ARRAY:
            return t->array_size * type_size(t->base);

        case TY_STRUCT: {
            TypeField *f = t->fields;
            u32 sz = 0;
            u32 max_align = 1;

            while (f) {
                u32 align = type_align(f->type);

                if (align > max_align) max_align = align;

                sz = (sz + align - 1) & ~(align - 1);
                sz += type_size(f->type);

                f = f->next;
            }

            sz = (sz + max_align - 1) & ~(max_align - 1);
            return sz;
        }

        default:
            return 0;
    }
}

static bool8 type_is_int(Type *t) {
    return t->kind >= TY_I8 && t->kind <= TY_U64;
}

static bool8 type_is_float(Type *t) {
    return t->kind == TY_F32 || t->kind == TY_F64;
}

static bool8 type_eq(Type *a, Type *b) {
    if (a == b) return TRUE;
    if (!a || !b) return FALSE;
    if (a->kind != b->kind) return FALSE;

    if (a->kind == TY_PTR) {
        return type_eq(a->base, b->base);
    }

    if (a->kind == TY_ARRAY) {
        return a->array_size == b->array_size && type_eq(a->base, b->base);
    }

    if (a->kind == TY_STRUCT) {
        if (a->name && b->name && strcmp(a->name, b->name) == 0) return TRUE;
        return FALSE;
    }

    return TRUE;
}

static const char *type_name(Type *t) {
    if (!t) return "?";

    switch (t->kind) {
        case TY_VOID:   return "vd";
        case TY_BOOL:   return "bl";
        case TY_I8:     return "i8";
        case TY_I16:    return "i16";
        case TY_I32:    return "i32";
        case TY_I64:    return "i64";
        case TY_U8:     return "u8";
        case TY_U16:    return "u16";
        case TY_U32:    return "u32";
        case TY_U64:    return "u64";
        case TY_F32:    return "f32";
        case TY_F64:    return "f64";
        case TY_CHAR:   return "ch";
        case TY_PTR:    return "pt";
        case TY_ARRAY:  return "arr";
        case TY_STRUCT: return t->name ? t->name : "struct";
        case TY_FN:     return "fn";
        default:        return "?";
    }
}

typedef enum {
    TOK_INT_LIT, TOK_FLOAT_LIT, TOK_CHAR_LIT, TOK_STR_LIT,
    TOK_IDENT,

    TOK_V, TOK_PV, TOK_PS, TOK_P, TOK_FN, TOK_RT,
    TOK_IF, TOK_EL, TOK_ELF, TOK_LP, TOK_FR, TOK_BK, TOK_SK,
    TOK_PT, TOK_DR, TOK_ST, TOK_AL, TOK_FF, TOK_IM, TOK_ASM,
    TOK_EX, TOK_CB, TOK_SZ, TOK_CT, TOK_NL, TOK_TR, TOK_FL_K,
    TOK_SC,

    TOK_ARCH, TOK_BITS, TOK_MODE, TOK_HEADER, TOK_RAW,

    TOK_TY_VOID, TOK_TY_BOOL,
    TOK_TY_I8, TOK_TY_I16, TOK_TY_I32, TOK_TY_I64,
    TOK_TY_U8, TOK_TY_U16, TOK_TY_U32, TOK_TY_U64,
    TOK_TY_F32, TOK_TY_F64,
    TOK_TY_CH, TOK_TY_STR, TOK_TY_PT,

    TOK_PLUS, TOK_MINUS, TOK_STAR, TOK_SLASH, TOK_PERCENT,
    TOK_AMP, TOK_PIPE, TOK_CARET, TOK_TILDE, TOK_BANG,
    TOK_LSHIFT, TOK_RSHIFT,
    TOK_EQ, TOK_NEQ, TOK_LT, TOK_GT, TOK_LTE, TOK_GTE,
    TOK_AND, TOK_OR,
    TOK_ASSIGN,
    TOK_PLUS_ASSIGN, TOK_MINUS_ASSIGN, TOK_STAR_ASSIGN, TOK_SLASH_ASSIGN,
    TOK_INC, TOK_DEC,
    TOK_ARROW,
    TOK_DOT,

    TOK_LPAREN, TOK_RPAREN,
    TOK_LBRACE, TOK_RBRACE,
    TOK_LBRACKET, TOK_RBRACKET,
    TOK_SEMI, TOK_COLON, TOK_COMMA, TOK_HASH,

    TOK_EOF,
    TOK_UNKNOWN
} TokenKind;

typedef struct {
    TokenKind   kind;
    int         line;
    int         col;
    char       *str_val;
    i64         int_val;
    double      float_val;
} Token;

typedef struct {
    const char *src;
    u32         pos;
    u32         len;
    int         line;
    int         col;
    Arena      *arena;
    Token      *tokens;
    u32         token_count;
    u32         token_cap;
} Lexer;

static struct { const char *kw; TokenKind tok; } g_keywords[] = {
    {"V",    TOK_V},   {"PV",  TOK_PV},  {"PS",   TOK_PS},
    {"P",    TOK_P},   {"FN",  TOK_FN},  {"RT",   TOK_RT},
    {"IF",   TOK_IF},  {"EL",  TOK_EL},  {"ELF",  TOK_ELF},
    {"LP",   TOK_LP},  {"FR",  TOK_FR},  {"BK",   TOK_BK},
    {"SK",   TOK_SK},  {"PT",  TOK_PT},  {"DR",   TOK_DR},
    {"ST",   TOK_ST},  {"AL",  TOK_AL},  {"FF",   TOK_FF},
    {"IM",   TOK_IM},  {"ASM", TOK_ASM}, {"EX",   TOK_EX},
    {"CB",   TOK_CB},  {"SZ",  TOK_SZ},  {"CT",   TOK_CT},
    {"NL",   TOK_NL},  {"TR",  TOK_TR},  {"FL",   TOK_FL_K},
    {"SC",   TOK_SC},

    {"ARCH",   TOK_ARCH},
    {"BITS",   TOK_BITS},
    {"MODE",   TOK_MODE},
    {"HEADER", TOK_HEADER},
    {"RAW",    TOK_RAW},

    {"vd",   TOK_TY_VOID}, {"bl", TOK_TY_BOOL},
    {"i8",   TOK_TY_I8},   {"i16", TOK_TY_I16},
    {"i32",  TOK_TY_I32},  {"i64", TOK_TY_I64},
    {"u8",   TOK_TY_U8},   {"u16", TOK_TY_U16},
    {"u32",  TOK_TY_U32},  {"u64", TOK_TY_U64},
    {"f32",  TOK_TY_F32},  {"f64", TOK_TY_F64},
    {"ch",   TOK_TY_CH},   {"str", TOK_TY_STR},
    {"pt",   TOK_TY_PT},

    {NULL, TOK_UNKNOWN}
};

static TokenKind keyword_lookup(const char *s) {
    int i;

    for (i = 0; g_keywords[i].kw; i++) {
        if (strcmp(g_keywords[i].kw, s) == 0) {
            return g_keywords[i].tok;
        }
    }

    return TOK_IDENT;
}

static void lexer_push(Lexer *l, Token t) {
    if (l->token_count >= l->token_cap) {
        l->token_cap = l->token_cap ? l->token_cap * 2 : 256;
        l->tokens    = (Token*)realloc(l->tokens, sizeof(Token) * l->token_cap);
    }

    l->tokens[l->token_count++] = t;
}

static char lexer_peek(Lexer *l) {
    return l->pos < l->len ? l->src[l->pos] : 0;
}

static char lexer_peek2(Lexer *l) {
    return l->pos + 1 < l->len ? l->src[l->pos + 1] : 0;
}

static char lexer_adv(Lexer *l) {
    char c = l->src[l->pos++];

    if (c == '\n') {
        l->line++;
        l->col = 1;
    } else {
        l->col++;
    }

    return c;
}

static void lexer_lex(Lexer *l) {
    while (l->pos < l->len) {
        char c;
        int ln, cl;

        while (l->pos < l->len && (
            l->src[l->pos] == ' '  ||
            l->src[l->pos] == '\t' ||
            l->src[l->pos] == '\r' ||
            l->src[l->pos] == '\n'
        )) {
            lexer_adv(l);
        }

        if (l->pos >= l->len) break;

        c = l->src[l->pos];
        ln = l->line;
        cl = l->col;

        if (c == '/' && lexer_peek2(l) == '/') {
            while (l->pos < l->len && l->src[l->pos] != '\n') l->pos++;
            continue;
        }

        if (c == '/' && lexer_peek2(l) == '*') {
            l->pos += 2;
            l->col += 2;

            while (l->pos + 1 < l->len && !(l->src[l->pos] == '*' && l->src[l->pos + 1] == '/')) {
                lexer_adv(l);
            }

            if (l->pos + 1 < l->len) {
                l->pos += 2;
                l->col += 2;
            }

            continue;
        }

        if (c == '"') {
            char buf[4096];
            u32 bi = 0;
            Token t;

            t.line = ln;
            t.col = cl;
            t.kind = TOK_STR_LIT;

            lexer_adv(l);

            while (l->pos < l->len && l->src[l->pos] != '"') {
                char ch = lexer_adv(l);

                if (ch == '\\') {
                    char esc = lexer_adv(l);

                    switch (esc) {
                        case 'n':  buf[bi++] = '\n'; break;
                        case 't':  buf[bi++] = '\t'; break;
                        case 'r':  buf[bi++] = '\r'; break;
                        case '0':  buf[bi++] = '\0'; break;
                        case '\\': buf[bi++] = '\\'; break;
                        case '"':  buf[bi++] = '"';  break;
                        default:   buf[bi++] = esc;  break;
                    }
                } else {
                    buf[bi++] = ch;
                }
            }

            if (l->pos < l->len) lexer_adv(l);

            buf[bi] = '\0';
            t.str_val = arena_strdup(l->arena, buf);
            lexer_push(l, t);

            continue;
        }

        if (c == '\'') {
            Token t;
            char esc;

            t.line = ln;
            t.col = cl;
            t.kind = TOK_CHAR_LIT;

            lexer_adv(l);

            if (l->src[l->pos] == '\\') {
                lexer_adv(l);
                esc = lexer_adv(l);

                switch (esc) {
                    case 'n': t.int_val = '\n'; break;
                    case 't': t.int_val = '\t'; break;
                    case '0': t.int_val = 0;     break;
                    default:  t.int_val = esc;   break;
                }
            } else {
                t.int_val = lexer_adv(l);
            }

            if (l->pos < l->len && l->src[l->pos] == '\'') lexer_adv(l);

            lexer_push(l, t);
            continue;
        }

        if (c >= '0' && c <= '9') {
            char buf[64];
            u32 bi = 0;
            Token t;
            bool8 is_float = FALSE;
            bool8 is_hex   = FALSE;

            t.line = ln;
            t.col = cl;

            if (c == '0' && (lexer_peek2(l) == 'x' || lexer_peek2(l) == 'X')) {
                buf[bi++] = lexer_adv(l);
                buf[bi++] = lexer_adv(l);
                is_hex = TRUE;

                while (l->pos < l->len && (
                    (l->src[l->pos] >= '0' && l->src[l->pos] <= '9') ||
                    (l->src[l->pos] >= 'a' && l->src[l->pos] <= 'f') ||
                    (l->src[l->pos] >= 'A' && l->src[l->pos] <= 'F')
                )) {
                    buf[bi++] = lexer_adv(l);
                }
            } else {
                while (l->pos < l->len && l->src[l->pos] >= '0' && l->src[l->pos] <= '9') {
                    buf[bi++] = lexer_adv(l);
                }

                if (l->pos < l->len && l->src[l->pos] == '.') {
                    is_float = TRUE;
                    buf[bi++] = lexer_adv(l);

                    while (l->pos < l->len && l->src[l->pos] >= '0' && l->src[l->pos] <= '9') {
                        buf[bi++] = lexer_adv(l);
                    }
                }
            }

            buf[bi] = '\0';

            if (is_float) {
                t.kind      = TOK_FLOAT_LIT;
                t.float_val = atof(buf);
            } else {
                t.kind    = TOK_INT_LIT;
                t.int_val = is_hex ? (i64)strtoll(buf, NULL, 16) : (i64)atoll(buf);
            }

            lexer_push(l, t);
            continue;
        }

        if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_') {
            char buf[256];
            u32 bi = 0;
            Token t;

            t.line = ln;
            t.col = cl;

            while (l->pos < l->len && (
                (l->src[l->pos] >= 'a' && l->src[l->pos] <= 'z') ||
                (l->src[l->pos] >= 'A' && l->src[l->pos] <= 'Z') ||
                (l->src[l->pos] >= '0' && l->src[l->pos] <= '9') ||
                l->src[l->pos] == '_'
            )) {
                buf[bi++] = lexer_adv(l);
            }

            buf[bi] = '\0';
            t.kind    = keyword_lookup(buf);
            t.str_val = arena_strdup(l->arena, buf);

            lexer_push(l, t);
            continue;
        }

        {
            Token t;

            t.line = ln;
            t.col = cl;
            t.str_val = NULL;
            t.int_val = 0;
            t.float_val = 0.0;

            lexer_adv(l);

            switch (c) {
                case '+':
                    if (lexer_peek(l) == '+') { lexer_adv(l); t.kind = TOK_INC; }
                    else if (lexer_peek(l) == '=') { lexer_adv(l); t.kind = TOK_PLUS_ASSIGN; }
                    else t.kind = TOK_PLUS;
                    break;

                case '-':
                    if (lexer_peek(l) == '-') { lexer_adv(l); t.kind = TOK_DEC; }
                    else if (lexer_peek(l) == '=') { lexer_adv(l); t.kind = TOK_MINUS_ASSIGN; }
                    else if (lexer_peek(l) == '>') { lexer_adv(l); t.kind = TOK_ARROW; }
                    else t.kind = TOK_MINUS;
                    break;

                case '*':
                    if (lexer_peek(l) == '=') { lexer_adv(l); t.kind = TOK_STAR_ASSIGN; }
                    else t.kind = TOK_STAR;
                    break;

                case '/':
                    if (lexer_peek(l) == '=') { lexer_adv(l); t.kind = TOK_SLASH_ASSIGN; }
                    else t.kind = TOK_SLASH;
                    break;

                case '%':
                    t.kind = TOK_PERCENT;
                    break;

                case '&':
                    if (lexer_peek(l) == '&') { lexer_adv(l); t.kind = TOK_AND; }
                    else t.kind = TOK_AMP;
                    break;

                case '|':
                    if (lexer_peek(l) == '|') { lexer_adv(l); t.kind = TOK_OR; }
                    else t.kind = TOK_PIPE;
                    break;

                case '^':
                    t.kind = TOK_CARET;
                    break;

                case '~':
                    t.kind = TOK_TILDE;
                    break;

                case '!':
                    if (lexer_peek(l) == '=') { lexer_adv(l); t.kind = TOK_NEQ; }
                    else t.kind = TOK_BANG;
                    break;

                case '<':
                    if (lexer_peek(l) == '<') { lexer_adv(l); t.kind = TOK_LSHIFT; }
                    else if (lexer_peek(l) == '=') { lexer_adv(l); t.kind = TOK_LTE; }
                    else t.kind = TOK_LT;
                    break;

                case '>':
                    if (lexer_peek(l) == '>') { lexer_adv(l); t.kind = TOK_RSHIFT; }
                    else if (lexer_peek(l) == '=') { lexer_adv(l); t.kind = TOK_GTE; }
                    else t.kind = TOK_GT;
                    break;

                case '=':
                    if (lexer_peek(l) == '=') { lexer_adv(l); t.kind = TOK_EQ; }
                    else t.kind = TOK_ASSIGN;
                    break;

                case '(': t.kind = TOK_LPAREN;   break;
                case ')': t.kind = TOK_RPAREN;   break;
                case '{': t.kind = TOK_LBRACE;   break;
                case '}': t.kind = TOK_RBRACE;   break;
                case '[': t.kind = TOK_LBRACKET; break;
                case ']': t.kind = TOK_RBRACKET; break;
                case ';': t.kind = TOK_SEMI;     break;
                case ':': t.kind = TOK_COLON;    break;
                case ',': t.kind = TOK_COMMA;    break;
                case '#': t.kind = TOK_HASH;     break;
                case '.': t.kind = TOK_DOT;      break;

                default:
                    t.kind = TOK_UNKNOWN;
                    WARN(ln, cl, "unexpected character '%c'", c);
                    break;
            }

            lexer_push(l, t);
        }
    }

    {
        Token t;

        t.kind = TOK_EOF;
        t.line = l->line;
        t.col = l->col;
        t.str_val = NULL;
        t.int_val = 0;
        t.float_val = 0.0;

        lexer_push(l, t);
    }
}

typedef enum {
    AST_BLOCK,
    AST_VAR_DECL,
    AST_ASSIGN,
    AST_IF,
    AST_LOOP,
    AST_FOR,
    AST_BREAK,
    AST_SKIP,
    AST_RETURN,
    AST_PRINT_VAR,
    AST_PRINT_STR,
    AST_PRINT_EXPR,
    AST_FN_DECL,
    AST_STRUCT_DECL,
    AST_IMPORT,
    AST_INLINE_ASM,
    AST_EXPR_STMT,
    AST_FREE,

    AST_TARGET,
    AST_RAW,
    AST_SYSCALL,

    AST_INT_LIT,
    AST_FLOAT_LIT,
    AST_CHAR_LIT,
    AST_STR_LIT,
    AST_BOOL_LIT,
    AST_NULL_LIT,
    AST_IDENT,
    AST_BINOP,
    AST_UNOP,
    AST_CALL,
    AST_INDEX,
    AST_FIELD,
    AST_ARROW,
    AST_DEREF,
    AST_ADDR,
    AST_ALLOC,
    AST_CAST,
    AST_SIZEOF,
    AST_ASSIGN_EXPR
} ASTKind;

typedef struct ASTNode ASTNode;

typedef struct {
    ASTNode **stmts;
    int       count;
    int       cap;
} ASTBlock;

typedef struct {
    char    *name;
    Type    *type;
    ASTNode *init;
} ASTVarDecl;

typedef struct {
    ASTNode *target;
    ASTNode *value;
    TokenKind op;
} ASTAssign;

typedef struct {
    ASTNode  *cond;
    ASTNode  *then_block;
    ASTNode **elif_conds;
    ASTNode **elif_blocks;
    int       elif_count;
    ASTNode  *else_block;
} ASTIf;

typedef struct {
    ASTNode *cond;
    ASTNode *body;
} ASTLoop;

typedef struct {
    ASTNode *init;
    ASTNode *cond;
    ASTNode *post;
    ASTNode *body;
} ASTFor;

typedef struct {
    ASTNode *value;
} ASTReturn;

typedef struct {
    char   *name;
    Type   *ret_type;
    char  **param_names;
    Type  **param_types;
    int     param_count;
    ASTNode *body;
    bool8   exported;
    bool8   is_variadic;
} ASTFnDecl;

typedef struct {
    char      *name;
    TypeField *fields;
} ASTStructDecl;

typedef struct {
    char *path;
} ASTImport;

typedef struct {
    char *code;
} ASTInlineAsm;

typedef struct {
    ASTNode *expr;
} ASTFree;

typedef struct {
    ASTNode *left;
    ASTNode *right;
    TokenKind op;
} ASTBinop;

typedef struct {
    ASTNode  *operand;
    TokenKind op;
    bool8     postfix;
} ASTUnop;

typedef struct {
    ASTNode  *callee;
    ASTNode **args;
    int       arg_count;
} ASTCall;

typedef struct {
    ASTNode *array;
    ASTNode *index;
} ASTIndex;

typedef struct {
    ASTNode *object;
    char    *field;
} ASTField;

typedef struct {
    ASTNode *ptr;
    char    *field;
} ASTArrow;

typedef struct {
    ASTNode *size_expr;
    Type    *type;
} ASTAlloc;

typedef struct {
    Type    *to_type;
    ASTNode *expr;
} ASTCast;

typedef struct {
    u8 *data;
    u32 len;
} ASTRaw;

struct ASTNode {
    ASTKind kind;
    int     line;
    int     col;
    Type   *resolved_type;

    union {
        i64          int_val;
        double       float_val;
        char        *str_val;
        bool8        bool_val;

        ASTBlock     block;
        ASTVarDecl   var_decl;
        ASTAssign    assign;
        ASTIf        if_stmt;
        ASTLoop      loop;
        ASTFor       for_stmt;
        ASTReturn    ret;
        ASTFnDecl    fn_decl;
        ASTStructDecl struct_decl;
        ASTImport    import_stmt;
        ASTInlineAsm asm_stmt;
        ASTFree      free_stmt;

        ASTBinop     binop;
        ASTUnop      unop;
        ASTCall      call;
        ASTIndex     index;
        ASTField     field;
        ASTArrow     arrow;
        ASTAlloc     alloc;
        ASTCast      cast;

        Type        *sizeof_type;
        char        *ident;
        ASTRaw       raw;
    };
};

static Arena g_ast_arena;

static ASTNode *ast_new(Arena *a, ASTKind kind, int line, int col) {
    ASTNode *n   = (ASTNode*)arena_alloc(a, sizeof(ASTNode));
    n->kind      = kind;
    n->line      = line;
    n->col       = col;
    n->resolved_type = NULL;
    return n;
}

typedef struct {
    Token  *tokens;
    u32     pos;
    u32     count;
    Arena  *arena;
} Parser;

static Token *p_peek(Parser *p) {
    return &p->tokens[p->pos];
}

static Token *p_peek2(Parser *p) {
    return p->pos + 1 < p->count ? &p->tokens[p->pos + 1] : &p->tokens[p->count - 1];
}

static Token *p_adv(Parser *p) {
    Token *t = &p->tokens[p->pos];

    if (p->pos + 1 < p->count) p->pos++;

    return t;
}

static bool8 p_check(Parser *p, TokenKind k) {
    return p_peek(p)->kind == k;
}

static bool8 p_match(Parser *p, TokenKind k) {
    if (p_check(p, k)) {
        p_adv(p);
        return TRUE;
    }

    return FALSE;
}

static Token *p_expect(Parser *p, TokenKind k, const char *msg) {
    if (!p_check(p, k)) {
        Token *t = p_peek(p);
        FATAL(t->line, t->col, "expected %s, got token kind %d", msg, t->kind);
    }

    return p_adv(p);
}

static ASTNode *parse_expr(Parser *p);
static ASTNode *parse_stmt(Parser *p);
static ASTNode *parse_block(Parser *p);

static Type *parse_type(Parser *p) {
    Token *t = p_adv(p);

    switch (t->kind) {
        case TOK_TY_VOID: return TY_VOID_T;
        case TOK_TY_BOOL: return TY_BOOL_T;
        case TOK_TY_I8:   return TY_I8_T;
        case TOK_TY_I16:  return TY_I16_T;
        case TOK_TY_I32:  return TY_I32_T;
        case TOK_TY_I64:  return TY_I64_T;
        case TOK_TY_U8:   return TY_U8_T;
        case TOK_TY_U16:  return TY_U16_T;
        case TOK_TY_U32:  return TY_U32_T;
        case TOK_TY_U64:  return TY_U64_T;
        case TOK_TY_F32:  return TY_F32_T;
        case TOK_TY_F64:  return TY_F64_T;
        case TOK_TY_CH:   return TY_CHAR_T;

        case TOK_TY_STR:
            return type_ptr(TY_CHAR_T);

        case TOK_TY_PT: {
            Type *base = TY_VOID_T;

            if (p_check(p, TOK_LT)) {
                p_adv(p);
                base = parse_type(p);
                p_expect(p, TOK_GT, ">");
            }

            return type_ptr(base);
        }

        case TOK_IDENT: {
            Type *ty = type_new(TY_STRUCT);
            ty->name = t->str_val;
            return ty;
        }

        default:
            FATAL(t->line, t->col, "expected type, got token kind %d", t->kind);
            return TY_VOID_T;
    }
}

static ASTNode *parse_primary(Parser *p) {
    Token *t = p_peek(p);
    ASTNode *n;

    switch (t->kind) {
        case TOK_INT_LIT:
            p_adv(p);
            n = ast_new(p->arena, AST_INT_LIT, t->line, t->col);
            n->int_val = t->int_val;
            return n;

        case TOK_FLOAT_LIT:
            p_adv(p);
            n = ast_new(p->arena, AST_FLOAT_LIT, t->line, t->col);
            n->float_val = t->float_val;
            return n;

        case TOK_CHAR_LIT:
            p_adv(p);
            n = ast_new(p->arena, AST_CHAR_LIT, t->line, t->col);
            n->int_val = t->int_val;
            return n;

        case TOK_STR_LIT:
            p_adv(p);
            n = ast_new(p->arena, AST_STR_LIT, t->line, t->col);
            n->str_val = t->str_val;
            return n;

        case TOK_TR:
            p_adv(p);
            n = ast_new(p->arena, AST_BOOL_LIT, t->line, t->col);
            n->bool_val = TRUE;
            return n;

        case TOK_FL_K:
            p_adv(p);
            n = ast_new(p->arena, AST_BOOL_LIT, t->line, t->col);
            n->bool_val = FALSE;
            return n;

        case TOK_NL:
            p_adv(p);
            n = ast_new(p->arena, AST_NULL_LIT, t->line, t->col);
            return n;

        case TOK_IDENT:
            p_adv(p);
            n = ast_new(p->arena, AST_IDENT, t->line, t->col);
            n->ident = t->str_val;
            return n;

        case TOK_LPAREN: {
            ASTNode *inner;

            p_adv(p);
            inner = parse_expr(p);
            p_expect(p, TOK_RPAREN, ")");

            return inner;
        }

        case TOK_AMP: {
            p_adv(p);
            n = ast_new(p->arena, AST_ADDR, t->line, t->col);
            n->unop.operand = parse_primary(p);
            n->unop.op = TOK_AMP;
            n->unop.postfix = FALSE;
            return n;
        }

        case TOK_DR: {
            p_adv(p);
            n = ast_new(p->arena, AST_DEREF, t->line, t->col);
            n->unop.operand = parse_primary(p);
            n->unop.op = TOK_STAR;
            n->unop.postfix = FALSE;
            return n;
        }

        case TOK_AL: {
            p_adv(p);
            n = ast_new(p->arena, AST_ALLOC, t->line, t->col);
            n->alloc.type = parse_type(p);
            n->alloc.size_expr = parse_expr(p);
            return n;
        }

        case TOK_SZ: {
            p_adv(p);
            p_expect(p, TOK_LPAREN, "(");
            n = ast_new(p->arena, AST_SIZEOF, t->line, t->col);
            n->sizeof_type = parse_type(p);
            p_expect(p, TOK_RPAREN, ")");
            return n;
        }

        case TOK_CT: {
            p_adv(p);
            p_expect(p, TOK_LPAREN, "(");
            n = ast_new(p->arena, AST_CAST, t->line, t->col);
            n->cast.to_type = parse_type(p);
            p_expect(p, TOK_COMMA, ",");
            n->cast.expr = parse_expr(p);
            p_expect(p, TOK_RPAREN, ")");
            return n;
        }

        case TOK_SC: {
            p_adv(p);

            n = ast_new(p->arena, AST_SYSCALL, t->line, t->col);
            n->call.callee = NULL;
            n->call.args = NULL;
            n->call.arg_count = 0;

            p_expect(p, TOK_LPAREN, "(");

            if (!p_check(p, TOK_RPAREN)) {
                int cap = 4;

                n->call.args = (ASTNode**)arena_alloc(p->arena, sizeof(ASTNode*) * cap);

                do {
                    if (n->call.arg_count >= cap) {
                        ASTNode **old = n->call.args;
                        int oldcap = cap;

                        cap *= 2;
                        n->call.args = (ASTNode**)arena_alloc(p->arena, sizeof(ASTNode*) * cap);
                        memcpy(n->call.args, old, sizeof(ASTNode*) * oldcap);
                    }

                    n->call.args[n->call.arg_count++] = parse_expr(p);

                } while (p_match(p, TOK_COMMA));
            }

            p_expect(p, TOK_RPAREN, ")");

            return n;
        }

        case TOK_MINUS:
        case TOK_BANG:
        case TOK_TILDE:
        case TOK_INC:
        case TOK_DEC: {
            p_adv(p);
            n = ast_new(p->arena, AST_UNOP, t->line, t->col);
            n->unop.op = t->kind;
            n->unop.operand = parse_primary(p);
            n->unop.postfix = FALSE;
            return n;
        }

        default:
            FATAL(t->line, t->col, "unexpected token kind %d in expression", t->kind);
            return NULL;
    }
}

static ASTNode *parse_postfix(Parser *p) {
    ASTNode *n = parse_primary(p);

    while (1) {
        Token *t = p_peek(p);

        if (t->kind == TOK_LPAREN) {
            ASTNode *call = ast_new(p->arena, AST_CALL, t->line, t->col);

            call->call.callee = n;
            call->call.args = NULL;
            call->call.arg_count = 0;

            p_adv(p);

            if (!p_check(p, TOK_RPAREN)) {
                int cap = 4;

                call->call.args = (ASTNode**)arena_alloc(p->arena, sizeof(ASTNode*) * cap);

                do {
                    if (call->call.arg_count >= cap) {
                        ASTNode **old = call->call.args;
                        int oldcap = cap;

                        cap *= 2;
                        call->call.args = (ASTNode**)arena_alloc(p->arena, sizeof(ASTNode*) * cap);
                        memcpy(call->call.args, old, sizeof(ASTNode*) * oldcap);
                    }

                    call->call.args[call->call.arg_count++] = parse_expr(p);

                } while (p_match(p, TOK_COMMA));
            }

            p_expect(p, TOK_RPAREN, ")");

            n = call;
        } else if (t->kind == TOK_LBRACKET) {
            ASTNode *idx = ast_new(p->arena, AST_INDEX, t->line, t->col);

            p_adv(p);

            idx->index.array = n;
            idx->index.index = parse_expr(p);

            p_expect(p, TOK_RBRACKET, "]");

            n = idx;
        } else if (t->kind == TOK_DOT) {
            ASTNode *fld = ast_new(p->arena, AST_FIELD, t->line, t->col);

            p_adv(p);

            fld->field.object = n;
            fld->field.field = p_expect(p, TOK_IDENT, "field name")->str_val;

            n = fld;
        } else if (t->kind == TOK_ARROW) {
            ASTNode *ar = ast_new(p->arena, AST_ARROW, t->line, t->col);

            p_adv(p);

            ar->arrow.ptr = n;
            ar->arrow.field = p_expect(p, TOK_IDENT, "field name")->str_val;

            n = ar;
        } else if (t->kind == TOK_INC || t->kind == TOK_DEC) {
            ASTNode *u = ast_new(p->arena, AST_UNOP, t->line, t->col);

            p_adv(p);

            u->unop.op = t->kind;
            u->unop.operand = n;
            u->unop.postfix = TRUE;

            n = u;
        } else {
            break;
        }
    }

    return n;
}

static int binop_prec(TokenKind k) {
    switch (k) {
        case TOK_OR:      return 1;
        case TOK_AND:     return 2;
        case TOK_PIPE:    return 3;
        case TOK_CARET:   return 4;
        case TOK_AMP:     return 5;

        case TOK_EQ:
        case TOK_NEQ:
            return 6;

        case TOK_LT:
        case TOK_GT:
        case TOK_LTE:
        case TOK_GTE:
            return 7;

        case TOK_LSHIFT:
        case TOK_RSHIFT:
            return 8;

        case TOK_PLUS:
        case TOK_MINUS:
            return 9;

        case TOK_STAR:
        case TOK_SLASH:
        case TOK_PERCENT:
            return 10;

        default:
            return -1;
    }
}

static ASTNode *parse_binop(Parser *p, int min_prec) {
    ASTNode *left = parse_postfix(p);

    while (1) {
        Token *t = p_peek(p);
        int prec = binop_prec(t->kind);

        if (prec < min_prec) break;

        {
            TokenKind op = t->kind;
            int ln = t->line;
            int cl = t->col;
            ASTNode *right;
            ASTNode *bin;

            p_adv(p);

            right = parse_binop(p, prec + 1);
            bin = ast_new(p->arena, AST_BINOP, ln, cl);

            bin->binop.left = left;
            bin->binop.right = right;
            bin->binop.op = op;

            left = bin;
        }
    }

    return left;
}

static ASTNode *parse_expr(Parser *p) {
    ASTNode *left = parse_binop(p, 0);
    Token *t = p_peek(p);

    if (
        t->kind == TOK_ASSIGN ||
        t->kind == TOK_PLUS_ASSIGN ||
        t->kind == TOK_MINUS_ASSIGN ||
        t->kind == TOK_STAR_ASSIGN ||
        t->kind == TOK_SLASH_ASSIGN
    ) {
        TokenKind op = t->kind;
        int ln = t->line;
        int cl = t->col;
        ASTNode *right;
        ASTNode *asgn;

        p_adv(p);

        right = parse_expr(p);
        asgn = ast_new(p->arena, AST_ASSIGN_EXPR, ln, cl);

        asgn->assign.target = left;
        asgn->assign.value = right;
        asgn->assign.op = op;

        return asgn;
    }

    return left;
}

static ASTNode *parse_block(Parser *p) {
    Token *t = p_expect(p, TOK_LBRACE, "{");
    ASTNode *blk = ast_new(p->arena, AST_BLOCK, t->line, t->col);

    blk->block.stmts = NULL;
    blk->block.count = 0;
    blk->block.cap = 0;

    while (!p_check(p, TOK_RBRACE) && !p_check(p, TOK_EOF)) {
        ASTNode *s = parse_stmt(p);

        if (!s) continue;

        if (blk->block.count >= blk->block.cap) {
            int newcap = blk->block.cap ? blk->block.cap * 2 : 8;
            ASTNode **old = blk->block.stmts;

            blk->block.stmts = (ASTNode**)arena_alloc(p->arena, sizeof(ASTNode*) * newcap);

            if (old) {
                memcpy(blk->block.stmts, old, sizeof(ASTNode*) * blk->block.count);
            }

            blk->block.cap = newcap;
        }

        blk->block.stmts[blk->block.count++] = s;
    }

    p_expect(p, TOK_RBRACE, "}");

    return blk;
}

static ASTNode *parse_stmt(Parser *p) {
    Token *t = p_peek(p);
    ASTNode *n;

    switch (t->kind) {
        case TOK_V: {
            p_adv(p);

            n = ast_new(p->arena, AST_VAR_DECL, t->line, t->col);
            n->var_decl.type = parse_type(p);
            n->var_decl.name = p_expect(p, TOK_IDENT, "variable name")->str_val;
            n->var_decl.init = NULL;

            if (p_match(p, TOK_ASSIGN)) {
                n->var_decl.init = parse_expr(p);
            }

            p_match(p, TOK_SEMI);
            return n;
        }

        case TOK_RT: {
            p_adv(p);

            n = ast_new(p->arena, AST_RETURN, t->line, t->col);
            n->ret.value = NULL;

            if (!p_check(p, TOK_SEMI) && !p_check(p, TOK_RBRACE)) {
                n->ret.value = parse_expr(p);
            }

            p_match(p, TOK_SEMI);
            return n;
        }

        case TOK_PV: {
            Token *nm;
            ASTNode *id;

            p_adv(p);

            n = ast_new(p->arena, AST_PRINT_VAR, t->line, t->col);
            nm = p_expect(p, TOK_IDENT, "variable name");

            id = ast_new(p->arena, AST_IDENT, nm->line, nm->col);
            id->ident = nm->str_val;

            n->unop.operand = id;

            p_match(p, TOK_SEMI);
            return n;
        }

        case TOK_PS: {
            p_adv(p);

            n = ast_new(p->arena, AST_PRINT_STR, t->line, t->col);
            n->str_val = p_expect(p, TOK_STR_LIT, "string literal")->str_val;

            p_match(p, TOK_SEMI);
            return n;
        }

        case TOK_P: {
            p_adv(p);

            n = ast_new(p->arena, AST_PRINT_EXPR, t->line, t->col);
            n->unop.operand = parse_expr(p);

            p_match(p, TOK_SEMI);
            return n;
        }

        case TOK_IF: {
            p_adv(p);

            n = ast_new(p->arena, AST_IF, t->line, t->col);

            n->if_stmt.cond = parse_expr(p);
            n->if_stmt.then_block = parse_block(p);

            n->if_stmt.elif_conds = NULL;
            n->if_stmt.elif_blocks = NULL;
            n->if_stmt.elif_count = 0;
            n->if_stmt.else_block = NULL;

            while (p_check(p, TOK_ELF)) {
                int ec;
                ASTNode **nc;
                ASTNode **nb;

                p_adv(p);

                ec = n->if_stmt.elif_count;

                nc = (ASTNode**)arena_alloc(p->arena, sizeof(ASTNode*) * (ec + 1));
                nb = (ASTNode**)arena_alloc(p->arena, sizeof(ASTNode*) * (ec + 1));

                if (ec) {
                    memcpy(nc, n->if_stmt.elif_conds, sizeof(ASTNode*) * ec);
                    memcpy(nb, n->if_stmt.elif_blocks, sizeof(ASTNode*) * ec);
                }

                nc[ec] = parse_expr(p);
                nb[ec] = parse_block(p);

                n->if_stmt.elif_conds = nc;
                n->if_stmt.elif_blocks = nb;
                n->if_stmt.elif_count++;
            }

            if (p_check(p, TOK_EL)) {
                p_adv(p);
                n->if_stmt.else_block = parse_block(p);
            }

            return n;
        }

        case TOK_LP: {
            p_adv(p);

            n = ast_new(p->arena, AST_LOOP, t->line, t->col);
            n->loop.cond = parse_expr(p);
            n->loop.body = parse_block(p);

            return n;
        }

        case TOK_FR: {
            p_adv(p);

            n = ast_new(p->arena, AST_FOR, t->line, t->col);

            n->for_stmt.init = parse_stmt(p);
            n->for_stmt.cond = parse_expr(p);

            p_match(p, TOK_SEMI);

            n->for_stmt.post = parse_expr(p);
            n->for_stmt.body = parse_block(p);

            return n;
        }

        case TOK_BK:
            p_adv(p);
            p_match(p, TOK_SEMI);
            return ast_new(p->arena, AST_BREAK, t->line, t->col);

        case TOK_SK:
            p_adv(p);
            p_match(p, TOK_SEMI);
            return ast_new(p->arena, AST_SKIP, t->line, t->col);

        case TOK_FN:
        case TOK_EX: {
            bool8 exported = (t->kind == TOK_EX);

            if (exported) {
                p_adv(p);
                t = p_peek(p);
            }

            p_adv(p);

            n = ast_new(p->arena, AST_FN_DECL, t->line, t->col);

            n->fn_decl.exported = exported;
            n->fn_decl.name = p_expect(p, TOK_IDENT, "function name")->str_val;

            n->fn_decl.param_names = NULL;
            n->fn_decl.param_types = NULL;
            n->fn_decl.param_count = 0;
            n->fn_decl.is_variadic = FALSE;

            p_expect(p, TOK_LPAREN, "(");

            if (!p_check(p, TOK_RPAREN)) {
                int cap = 4;
                char **pnames = (char**)arena_alloc(p->arena, sizeof(char*) * cap);
                Type **ptypes = (Type**)arena_alloc(p->arena, sizeof(Type*) * cap);

                do {
                    Type *pt;
                    char *pn;

                    if (p_check(p, TOK_DOT) && p_peek2(p)->kind == TOK_DOT) {
                        p_adv(p);
                        p_adv(p);
                        p_adv(p);

                        n->fn_decl.is_variadic = TRUE;
                        break;
                    }

                    pt = parse_type(p);
                    pn = p_expect(p, TOK_IDENT, "param name")->str_val;

                    if (n->fn_decl.param_count >= cap) {
                        char **on = pnames;
                        Type **ot = ptypes;

                        cap *= 2;

                        pnames = (char**)arena_alloc(p->arena, sizeof(char*) * cap);
                        ptypes = (Type**)arena_alloc(p->arena, sizeof(Type*) * cap);

                        memcpy(pnames, on, sizeof(char*) * n->fn_decl.param_count);
                        memcpy(ptypes, ot, sizeof(Type*) * n->fn_decl.param_count);
                    }

                    ptypes[n->fn_decl.param_count] = pt;
                    pnames[n->fn_decl.param_count] = pn;
                    n->fn_decl.param_count++;

                } while (p_match(p, TOK_COMMA));

                n->fn_decl.param_names = pnames;
                n->fn_decl.param_types = ptypes;
            }

            p_expect(p, TOK_RPAREN, ")");

            n->fn_decl.ret_type = TY_VOID_T;

            if (!p_check(p, TOK_LBRACE)) {
                n->fn_decl.ret_type = parse_type(p);
            }

            n->fn_decl.body = parse_block(p);

            return n;
        }

        case TOK_ST: {
            TypeField *last = NULL;

            p_adv(p);

            n = ast_new(p->arena, AST_STRUCT_DECL, t->line, t->col);
            n->struct_decl.name = p_expect(p, TOK_IDENT, "struct name")->str_val;
            n->struct_decl.fields = NULL;

            p_expect(p, TOK_LBRACE, "{");

            while (!p_check(p, TOK_RBRACE) && !p_check(p, TOK_EOF)) {
                TypeField *f = (TypeField*)arena_alloc(p->arena, sizeof(TypeField));

                f->type = parse_type(p);
                f->name = p_expect(p, TOK_IDENT, "field name")->str_val;
                f->next = NULL;

                p_match(p, TOK_SEMI);

                if (!last) n->struct_decl.fields = f;
                else last->next = f;

                last = f;
            }

            p_expect(p, TOK_RBRACE, "}");

            return n;
        }

        case TOK_IM: {
            p_adv(p);

            n = ast_new(p->arena, AST_IMPORT, t->line, t->col);
            n->import_stmt.path = p_expect(p, TOK_STR_LIT, "path string")->str_val;

            p_match(p, TOK_SEMI);
            return n;
        }

        case TOK_ASM: {
            FATAL(t->line, t->col, "ASM is disabled; use SC(...) for syscalls");
            return NULL;
        }

        case TOK_FF: {
            p_adv(p);

            n = ast_new(p->arena, AST_FREE, t->line, t->col);
            n->free_stmt.expr = parse_expr(p);

            p_match(p, TOK_SEMI);
            return n;
        }

        default: {
            ASTNode *expr = parse_expr(p);

            p_match(p, TOK_SEMI);

            n = ast_new(p->arena, AST_EXPR_STMT, expr->line, expr->col);
            n->unop.operand = expr;

            return n;
        }
    }
}

static ASTNode *parse_program(Parser *p) {
    ASTNode *prog = ast_new(p->arena, AST_BLOCK, 1, 1);

    prog->block.stmts = NULL;
    prog->block.count = 0;
    prog->block.cap = 0;

    while (!p_check(p, TOK_EOF)) {
        ASTNode *s = parse_stmt(p);

        if (!s) continue;

        if (prog->block.count >= prog->block.cap) {
            int nc = prog->block.cap ? prog->block.cap * 2 : 16;
            ASTNode **old = prog->block.stmts;

            prog->block.stmts = (ASTNode**)arena_alloc(p->arena, sizeof(ASTNode*) * nc);

            if (old) {
                memcpy(prog->block.stmts, old, sizeof(ASTNode*) * prog->block.count);
            }

            prog->block.cap = nc;
        }

        prog->block.stmts[prog->block.count++] = s;
    }

    return prog;
}

typedef enum {
    SYM_VAR,
    SYM_FN,
    SYM_STRUCT,
    SYM_PARAM
} SymKind;

typedef struct Symbol Symbol;

struct Symbol {
    char    *name;
    SymKind  kind;
    Type    *type;
    int      scope_depth;

    i32      stack_offset;
    u32      data_offset;
    bool8    is_global;

    Symbol  *next;
};

#define SYM_TABLE_SIZE 512

typedef struct Scope Scope;

struct Scope {
    Symbol  *buckets[SYM_TABLE_SIZE];
    Scope   *parent;
    int      depth;
};

typedef struct {
    Scope  *current;
    Arena  *arena;
} SymTable;

static void symtable_init(SymTable *st, Arena *a) {
    st->arena = a;
    st->current = NULL;
}

static void symtable_push(SymTable *st) {
    Scope *s = (Scope*)arena_alloc(st->arena, sizeof(Scope));

    memset(s->buckets, 0, sizeof(s->buckets));

    s->parent = st->current;
    s->depth = st->current ? st->current->depth + 1 : 0;

    st->current = s;
}

static void symtable_pop(SymTable *st) {
    if (st->current) st->current = st->current->parent;
}

static u32 sym_hash(const char *s) {
    u32 h = 2166136261u;

    while (*s) {
        h ^= (u8)*s++;
        h *= 16777619u;
    }

    return h % SYM_TABLE_SIZE;
}

static Symbol *symtable_lookup(SymTable *st, const char *name) {
    Scope *sc = st->current;
    u32 h = sym_hash(name);

    while (sc) {
        Symbol *sym = sc->buckets[h];

        while (sym) {
            if (strcmp(sym->name, name) == 0) return sym;
            sym = sym->next;
        }

        sc = sc->parent;
    }

    return NULL;
}

static Symbol *symtable_lookup_local(SymTable *st, const char *name) {
    u32 h = sym_hash(name);
    Symbol *sym = st->current->buckets[h];

    while (sym) {
        if (strcmp(sym->name, name) == 0) return sym;
        sym = sym->next;
    }

    return NULL;
}

static Symbol *symtable_define(SymTable *st, const char *name, SymKind kind, Type *type) {
    u32 h;
    Symbol *sym;

    if (symtable_lookup_local(st, name)) return NULL;

    h = sym_hash(name);

    sym = (Symbol*)arena_alloc(st->arena, sizeof(Symbol));

    sym->name = arena_strdup(st->arena, name);
    sym->kind = kind;
    sym->type = type;
    sym->scope_depth = st->current->depth;

    sym->stack_offset = 0;
    sym->data_offset = 0;
    sym->is_global = (st->current->parent == NULL);

    sym->next = st->current->buckets[h];
    st->current->buckets[h] = sym;

    return sym;
}

typedef struct {
    SymTable *syms;
    Arena    *arena;
    Type     *current_fn_ret;
    bool8     in_loop;
} Semantic;

static Type *resolve_type_name(Semantic *sem, const char *name) {
    Symbol *s = symtable_lookup(sem->syms, name);

    if (s && s->kind == SYM_STRUCT) return s->type;

    return NULL;
}

static Type *sem_resolve_type(Semantic *sem, Type *t) {
    if (!t) return t;

    if (t->kind == TY_STRUCT && t->name && !t->fields) {
        Type *r = resolve_type_name(sem, t->name);
        if (r) return r;
    }

    if (t->base) {
        t->base = sem_resolve_type(sem, t->base);
    }

    return t;
}

static Type *sem_expr(Semantic *sem, ASTNode *n);
static void  sem_stmt(Semantic *sem, ASTNode *n);
static void  sem_block(Semantic *sem, ASTNode *n);

static Type *sem_expr(Semantic *sem, ASTNode *n) {
    if (!n) return TY_VOID_T;

    switch (n->kind) {
        case AST_INT_LIT:
            n->resolved_type = TY_I64_T;
            return TY_I64_T;

        case AST_FLOAT_LIT:
            n->resolved_type = TY_F64_T;
            return TY_F64_T;

        case AST_CHAR_LIT:
            n->resolved_type = TY_CHAR_T;
            return TY_CHAR_T;

        case AST_BOOL_LIT:
            n->resolved_type = TY_BOOL_T;
            return TY_BOOL_T;

        case AST_NULL_LIT:
            n->resolved_type = type_ptr(TY_VOID_T);
            return n->resolved_type;

        case AST_STR_LIT:
            n->resolved_type = type_ptr(TY_CHAR_T);
            return n->resolved_type;

        case AST_IDENT: {
            Symbol *s = symtable_lookup(sem->syms, n->ident);

            if (!s) {
                ERROR(n->line, n->col, "undefined identifier '%s'", n->ident);
                return TY_UNKNOWN_T;
            }

            n->resolved_type = s->type;
            return s->type;
        }

        case AST_BINOP: {
            Type *lt = sem_expr(sem, n->binop.left);
            Type *rt = sem_expr(sem, n->binop.right);

            switch (n->binop.op) {
                case TOK_EQ:
                case TOK_NEQ:
                case TOK_LT:
                case TOK_GT:
                case TOK_LTE:
                case TOK_GTE:
                case TOK_AND:
                case TOK_OR:
                    n->resolved_type = TY_BOOL_T;
                    return TY_BOOL_T;

                default:
                    break;
            }

            if (lt->kind == TY_F64 || rt->kind == TY_F64) {
                n->resolved_type = TY_F64_T;
            } else if (lt->kind == TY_F32 || rt->kind == TY_F32) {
                n->resolved_type = TY_F32_T;
            } else if (lt->kind == TY_I64 || rt->kind == TY_I64) {
                n->resolved_type = TY_I64_T;
            } else {
                n->resolved_type = lt;
            }

            return n->resolved_type;
        }

        case AST_UNOP: {
            Type *t = sem_expr(sem, n->unop.operand);

            if (n->unop.op == TOK_AMP) {
                n->resolved_type = type_ptr(t);
                return n->resolved_type;
            }

            if (n->unop.op == TOK_STAR || n->unop.op == TOK_DR) {
                if (t->kind != TY_PTR) {
                    ERROR(n->line, n->col, "dereference of non-pointer");
                }

                n->resolved_type = t->kind == TY_PTR ? t->base : TY_UNKNOWN_T;
                return n->resolved_type;
            }

            n->resolved_type = t;
            return t;
        }

        case AST_ADDR: {
            Type *t = sem_expr(sem, n->unop.operand);
            n->resolved_type = type_ptr(t);
            return n->resolved_type;
        }

        case AST_DEREF: {
            Type *t = sem_expr(sem, n->unop.operand);

            if (t->kind != TY_PTR) {
                ERROR(n->line, n->col, "DR on non-pointer");
            }

            n->resolved_type = t->kind == TY_PTR ? t->base : TY_UNKNOWN_T;
            return n->resolved_type;
        }

        case AST_CALL: {
            Type *ct = sem_expr(sem, n->call.callee);
            int i;

            for (i = 0; i < n->call.arg_count; i++) {
                sem_expr(sem, n->call.args[i]);
            }

            if (ct->kind == TY_FN) {
                n->resolved_type = ct->ret_type;
                return ct->ret_type;
            }

            if (n->call.callee->kind == AST_IDENT) {
                Symbol *s = symtable_lookup(sem->syms, n->call.callee->ident);

                if (s && s->type->kind == TY_FN) {
                    n->resolved_type = s->type->ret_type;
                    return s->type->ret_type;
                }
            }

            n->resolved_type = TY_UNKNOWN_T;
            return TY_UNKNOWN_T;
        }

        case AST_SYSCALL: {
            int i;

            if (n->call.arg_count < 1) {
                ERROR(n->line, n->col, "SC requires a syscall number");
            }

            if (n->call.arg_count > 7) {
                ERROR(n->line, n->col, "SC supports at most 7 arguments: number + up to 6 args");
            }

            for (i = 0; i < n->call.arg_count; i++) {
                sem_expr(sem, n->call.args[i]);
            }

            n->resolved_type = TY_I64_T;
            return TY_I64_T;
        }

        case AST_INDEX: {
            Type *at = sem_expr(sem, n->index.array);

            sem_expr(sem, n->index.index);

            if (at->kind == TY_PTR) {
                n->resolved_type = at->base;
            } else if (at->kind == TY_ARRAY) {
                n->resolved_type = at->base;
            } else {
                ERROR(n->line, n->col, "index of non-array/pointer");
                n->resolved_type = TY_UNKNOWN_T;
            }

            return n->resolved_type;
        }

        case AST_FIELD: {
            Type *ot = sem_expr(sem, n->field.object);
            TypeField *f;

            if (ot->kind != TY_STRUCT) {
                ERROR(n->line, n->col, "field access on non-struct");
                n->resolved_type = TY_UNKNOWN_T;
                return TY_UNKNOWN_T;
            }

            f = ot->fields;

            while (f) {
                if (strcmp(f->name, n->field.field) == 0) {
                    n->resolved_type = f->type;
                    return f->type;
                }

                f = f->next;
            }

            ERROR(n->line, n->col, "no field '%s' in struct '%s'", n->field.field, ot->name);
            n->resolved_type = TY_UNKNOWN_T;
            return TY_UNKNOWN_T;
        }

        case AST_ARROW: {
            Type *pt = sem_expr(sem, n->arrow.ptr);
            Type *st = (pt->kind == TY_PTR) ? pt->base : pt;
            TypeField *f;

            if (st->kind != TY_STRUCT) {
                ERROR(n->line, n->col, "arrow on non-struct-pointer");
                n->resolved_type = TY_UNKNOWN_T;
                return TY_UNKNOWN_T;
            }

            f = st->fields;

            while (f) {
                if (strcmp(f->name, n->arrow.field) == 0) {
                    n->resolved_type = f->type;
                    return f->type;
                }

                f = f->next;
            }

            ERROR(n->line, n->col, "no field '%s'", n->arrow.field);
            n->resolved_type = TY_UNKNOWN_T;
            return TY_UNKNOWN_T;
        }

        case AST_ALLOC: {
            n->alloc.type = sem_resolve_type(sem, n->alloc.type);
            sem_expr(sem, n->alloc.size_expr);

            n->resolved_type = type_ptr(n->alloc.type);
            return n->resolved_type;
        }

        case AST_CAST: {
            n->cast.to_type = sem_resolve_type(sem, n->cast.to_type);
            sem_expr(sem, n->cast.expr);

            n->resolved_type = n->cast.to_type;
            return n->resolved_type;
        }

        case AST_SIZEOF: {
            n->sizeof_type = sem_resolve_type(sem, n->sizeof_type);
            n->resolved_type = TY_U64_T;
            return TY_U64_T;
        }

        case AST_ASSIGN_EXPR: {
            Type *vt;

            sem_expr(sem, n->assign.target);
            vt = sem_expr(sem, n->assign.value);

            n->resolved_type = vt;
            return vt;
        }

        default:
            n->resolved_type = TY_UNKNOWN_T;
            return TY_UNKNOWN_T;
    }
}

static void sem_stmt(Semantic *sem, ASTNode *n) {
    if (!n) return;

    switch (n->kind) {
        case AST_BLOCK:
            sem_block(sem, n);
            return;

        case AST_VAR_DECL: {
            if (n->var_decl.init) sem_expr(sem, n->var_decl.init);

            n->var_decl.type = sem_resolve_type(sem, n->var_decl.type);

            {
                Symbol *s = symtable_define(sem->syms, n->var_decl.name, SYM_VAR, n->var_decl.type);

                if (!s) {
                    ERROR(n->line, n->col, "redefinition of '%s'", n->var_decl.name);
                }
            }

            return;
        }

        case AST_EXPR_STMT:
        case AST_PRINT_VAR:
        case AST_PRINT_EXPR:
            sem_expr(sem, n->unop.operand);
            return;

        case AST_PRINT_STR:
            return;

        case AST_RETURN:
            if (n->ret.value) {
                Type *rt = sem_expr(sem, n->ret.value);

                if (
                    sem->current_fn_ret &&
                    !type_eq(rt, sem->current_fn_ret) &&
                    sem->current_fn_ret->kind != TY_VOID
                ) {
                    WARN(n->line, n->col, "return type mismatch");
                }
            }
            return;

        case AST_IF: {
            int i;

            sem_expr(sem, n->if_stmt.cond);
            sem_block(sem, n->if_stmt.then_block);

            for (i = 0; i < n->if_stmt.elif_count; i++) {
                sem_expr(sem, n->if_stmt.elif_conds[i]);
                sem_block(sem, n->if_stmt.elif_blocks[i]);
            }

            if (n->if_stmt.else_block) sem_block(sem, n->if_stmt.else_block);

            return;
        }

        case AST_LOOP: {
            bool8 old;

            sem_expr(sem, n->loop.cond);

            old = sem->in_loop;
            sem->in_loop = TRUE;

            sem_block(sem, n->loop.body);

            sem->in_loop = old;
            return;
        }

        case AST_FOR: {
            bool8 old;

            symtable_push(sem->syms);

            sem_stmt(sem, n->for_stmt.init);
            sem_expr(sem, n->for_stmt.cond);
            sem_expr(sem, n->for_stmt.post);

            old = sem->in_loop;
            sem->in_loop = TRUE;

            sem_block(sem, n->for_stmt.body);

            sem->in_loop = old;

            symtable_pop(sem->syms);
            return;
        }

        case AST_BREAK:
            if (!sem->in_loop) WARN(n->line, n->col, "BK outside loop");
            return;

        case AST_SKIP:
            if (!sem->in_loop) WARN(n->line, n->col, "SK outside loop");
            return;

        case AST_FN_DECL: {
            Type *fnt;
            Type *old_ret;
            int i;

            n->fn_decl.ret_type = sem_resolve_type(sem, n->fn_decl.ret_type);

            for (i = 0; i < n->fn_decl.param_count; i++) {
                n->fn_decl.param_types[i] = sem_resolve_type(sem, n->fn_decl.param_types[i]);
            }

            fnt = type_new(TY_FN);
            fnt->ret_type = n->fn_decl.ret_type;
            fnt->param_count = n->fn_decl.param_count;
            fnt->param_types = n->fn_decl.param_types;

            symtable_define(sem->syms, n->fn_decl.name, SYM_FN, fnt);

            symtable_push(sem->syms);

            for (i = 0; i < n->fn_decl.param_count; i++) {
                symtable_define(
                    sem->syms,
                    n->fn_decl.param_names[i],
                    SYM_PARAM,
                    n->fn_decl.param_types[i]
                );
            }

            old_ret = sem->current_fn_ret;
            sem->current_fn_ret = n->fn_decl.ret_type;

            sem_block(sem, n->fn_decl.body);

            sem->current_fn_ret = old_ret;

            symtable_pop(sem->syms);
            return;
        }

        case AST_STRUCT_DECL: {
            Type *st = type_new(TY_STRUCT);
            Symbol *s;
            TypeField *f;

            st->name = n->struct_decl.name;

            s = symtable_define(sem->syms, n->struct_decl.name, SYM_STRUCT, st);

            if (!s) {
                ERROR(n->line, n->col, "redefinition of struct '%s'", n->struct_decl.name);
            }

            f = n->struct_decl.fields;

            while (f) {
                f->type = sem_resolve_type(sem, f->type);
                f = f->next;
            }

            st->fields = n->struct_decl.fields;
            return;
        }

        case AST_FREE:
            sem_expr(sem, n->free_stmt.expr);
            return;

        case AST_IMPORT:
            return;

        case AST_INLINE_ASM:
            FATAL(n->line, n->col, "ASM is disabled; use SC(...) for syscalls");
            return;

        case AST_TARGET:
            return;

        case AST_RAW:
            return;

        default:
            return;
    }
}

static void sem_block(Semantic *sem, ASTNode *n) {
    int i;

    symtable_push(sem->syms);

    for (i = 0; i < n->block.count; i++) {
        sem_stmt(sem, n->block.stmts[i]);
    }

    symtable_pop(sem->syms);
}

typedef enum {
    IR_NOP,
    IR_LABEL,
    IR_CONST_INT,
    IR_CONST_FLOAT,
    IR_CONST_STR,
    IR_LOAD,
    IR_STORE,
    IR_LOAD_ADDR,
    IR_DEREF,

    IR_ADD, IR_SUB, IR_MUL, IR_DIV, IR_MOD,
    IR_AND, IR_OR, IR_XOR, IR_NOT, IR_NEG,
    IR_SHL, IR_SHR,

    IR_EQ, IR_NEQ, IR_LT, IR_GT, IR_LTE, IR_GTE,
    IR_BOOL_AND, IR_BOOL_OR,

    IR_JMP,
    IR_JZ,
    IR_JNZ,

    IR_CALL,
    IR_RET,

    IR_ALLOCA,
    IR_MALLOC,
    IR_FREE,

    IR_CAST,
    IR_FIELD_PTR,
    IR_INDEX_PTR,
    IR_PHI,

    IR_INLINE_ASM,

    IR_PRINT_INT,
    IR_PRINT_STR,
    IR_PRINT_FLOAT,

    IR_FN_BEGIN,
    IR_FN_END,
    IR_PARAM,
    IR_SYSCALL
} IROp;

typedef enum {
    IRVAL_REG,
    IRVAL_CONST_INT,
    IRVAL_CONST_FLOAT,
    IRVAL_LABEL,
    IRVAL_STR,
    IRVAL_NONE
} IRValKind;

typedef struct IRVal {
    IRValKind kind;
    u32       reg;
    i64       ival;
    double    fval;
    char     *sval;
    Type     *type;
} IRVal;

#define IRVAL_NONE_V ((IRVal){IRVAL_NONE,0,0,0.0,NULL,NULL})

typedef struct IRInstr {
    IROp    op;

    IRVal   dst;
    IRVal   src1;
    IRVal   src2;

    char   *label;
    char   *fn_name;

    int     arg_count;
    IRVal  *args;

    Type   *cast_type;
    Type   *alloc_type;

    u32     field_idx;
    char   *asm_code;
} IRInstr;

typedef struct {
    IRInstr *instrs;
    u32      count;
    u32      cap;
    u32      next_reg;
    u32      next_label;
    Arena   *arena;
} IRBuilder;

static void ir_init(IRBuilder *b, Arena *a) {
    b->instrs = NULL;
    b->count = 0;
    b->cap = 0;
    b->next_reg = 0;
    b->next_label = 0;
    b->arena = a;
}

static IRInstr *ir_emit(IRBuilder *b) {
    IRInstr *ins;

    if (b->count >= b->cap) {
        b->cap = b->cap ? b->cap * 2 : 256;
        b->instrs = (IRInstr*)realloc(b->instrs, sizeof(IRInstr) * b->cap);
    }

    ins = &b->instrs[b->count++];
    memset(ins, 0, sizeof(IRInstr));

    return ins;
}

static IRVal ir_new_reg(IRBuilder *b, Type *t) {
    IRVal v;

    v.kind = IRVAL_REG;
    v.reg = b->next_reg++;
    v.type = t;

    v.ival = 0;
    v.fval = 0.0;
    v.sval = NULL;

    return v;
}

static char *ir_new_label(IRBuilder *b, const char *prefix) {
    char buf[64];

    sprintf(buf, "%s_%u", prefix, b->next_label++);

    return arena_strdup(b->arena, buf);
}

static IRVal ir_const_int(i64 v, Type *t) {
    IRVal val;

    val.kind = IRVAL_CONST_INT;
    val.ival = v;
    val.type = t;

    val.reg = 0;
    val.fval = 0.0;
    val.sval = NULL;

    return val;
}

static IRVal ir_const_float(double v, Type *t) {
    IRVal val;

    val.kind = IRVAL_CONST_FLOAT;
    val.fval = v;
    val.type = t;

    val.reg = 0;
    val.ival = 0;
    val.sval = NULL;

    return val;
}

static IRVal ir_label_val(char *lbl) {
    IRVal val;

    val.kind = IRVAL_LABEL;
    val.sval = lbl;
    val.type = NULL;

    val.reg = 0;
    val.ival = 0;
    val.fval = 0.0;

    return val;
}

static IRVal ir_str_val(char *s) {
    IRVal val;

    val.kind = IRVAL_STR;
    val.sval = s;
    val.type = NULL;

    val.reg = 0;
    val.ival = 0;
    val.fval = 0.0;

    return val;
}

#define IRMAP_SIZE 512

typedef struct {
    char *name;
    IRVal val;
} IRMapEntry;

typedef struct IRScope IRScope;

struct IRScope {
    IRMapEntry entries[IRMAP_SIZE];
    int        count;
    IRScope   *parent;
};

static IRScope *irscope_new(Arena *a, IRScope *parent) {
    IRScope *s = (IRScope*)arena_alloc(a, sizeof(IRScope));

    s->count = 0;
    s->parent = parent;

    return s;
}

static void irscope_set(IRScope *s, const char *name, IRVal val) {
    int i;

    for (i = 0; i < s->count; i++) {
        if (strcmp(s->entries[i].name, name) == 0) {
            s->entries[i].val = val;
            return;
        }
    }

    if (s->count < IRMAP_SIZE) {
        s->entries[s->count].name = (char*)name;
        s->entries[s->count].val = val;
        s->count++;
    }
}

static bool8 irscope_get(IRScope *s, const char *name, IRVal *out) {
    int i;
    IRScope *cur = s;

    while (cur) {
        for (i = 0; i < cur->count; i++) {
            if (strcmp(cur->entries[i].name, name) == 0) {
                *out = cur->entries[i].val;
                return TRUE;
            }
        }

        cur = cur->parent;
    }

    return FALSE;
}

typedef struct {
    IRBuilder *b;
    Arena     *arena;
    IRScope   *scope;

    char     **break_stack;
    char     **cont_stack;
    int        loop_depth;
    int        loop_cap;
} IRLower;

static IRVal lower_expr(IRLower *l, ASTNode *n);
static void  lower_stmt(IRLower *l, ASTNode *n);

static void lower_push_loop(IRLower *l, char *brk, char *cont) {
    if (l->loop_depth >= l->loop_cap) {
        int newcap = l->loop_cap ? l->loop_cap * 2 : 8;

        l->break_stack = (char**)realloc(l->break_stack, sizeof(char*) * newcap);
        l->cont_stack  = (char**)realloc(l->cont_stack, sizeof(char*) * newcap);

        l->loop_cap = newcap;
    }

    l->break_stack[l->loop_depth] = brk;
    l->cont_stack[l->loop_depth] = cont;
    l->loop_depth++;
}

static void lower_pop_loop(IRLower *l) {
    if (l->loop_depth > 0) l->loop_depth--;
}

static char *lower_current_break(IRLower *l) {
    if (l->loop_depth <= 0) return NULL;
    return l->break_stack[l->loop_depth - 1];
}

static char *lower_current_cont(IRLower *l) {
    if (l->loop_depth <= 0) return NULL;
    return l->cont_stack[l->loop_depth - 1];
}

static IRVal lower_expr(IRLower *l, ASTNode *n) {
    IRBuilder *b = l->b;
    IRInstr   *ins;
    IRVal      dst;

    if (!n) return IRVAL_NONE_V;

    switch (n->kind) {
        case AST_INT_LIT:
            return ir_const_int(n->int_val, n->resolved_type ? n->resolved_type : TY_I64_T);

        case AST_FLOAT_LIT:
            return ir_const_float(n->float_val, n->resolved_type ? n->resolved_type : TY_F64_T);

        case AST_CHAR_LIT:
            return ir_const_int(n->int_val, TY_CHAR_T);

        case AST_BOOL_LIT:
            return ir_const_int(n->bool_val ? 1 : 0, TY_BOOL_T);

        case AST_NULL_LIT:
            return ir_const_int(0, type_ptr(TY_VOID_T));

        case AST_STR_LIT: {
            dst = ir_new_reg(b, type_ptr(TY_CHAR_T));

            ins = ir_emit(b);
            ins->op = IR_CONST_STR;
            ins->dst = dst;
            ins->src1 = ir_str_val(n->str_val);

            return dst;
        }

        case AST_IDENT: {
            IRVal addr;

            if (!irscope_get(l->scope, n->ident, &addr)) {
                dst = ir_new_reg(b, n->resolved_type ? n->resolved_type : TY_I64_T);

                ins = ir_emit(b);
                ins->op = IR_LOAD;
                ins->dst = dst;
                ins->label = n->ident;

                return dst;
            }

            if (addr.kind == IRVAL_REG) {
                dst = ir_new_reg(b, n->resolved_type ? n->resolved_type : TY_I64_T);

                ins = ir_emit(b);
                ins->op = IR_DEREF;
                ins->dst = dst;
                ins->src1 = addr;

                return dst;
            }

            return addr;
        }

        case AST_BINOP: {
            IRVal lv = lower_expr(l, n->binop.left);
            IRVal rv = lower_expr(l, n->binop.right);

            dst = ir_new_reg(b, n->resolved_type ? n->resolved_type : TY_I64_T);
            ins = ir_emit(b);

            switch (n->binop.op) {
                case TOK_PLUS:    ins->op = IR_ADD; break;
                case TOK_MINUS:   ins->op = IR_SUB; break;
                case TOK_STAR:    ins->op = IR_MUL; break;
                case TOK_SLASH:   ins->op = IR_DIV; break;
                case TOK_PERCENT: ins->op = IR_MOD; break;
                case TOK_AMP:     ins->op = IR_AND; break;
                case TOK_PIPE:    ins->op = IR_OR;  break;
                case TOK_CARET:   ins->op = IR_XOR; break;
                case TOK_LSHIFT:  ins->op = IR_SHL; break;
                case TOK_RSHIFT:  ins->op = IR_SHR; break;
                case TOK_EQ:      ins->op = IR_EQ;  break;
                case TOK_NEQ:     ins->op = IR_NEQ; break;
                case TOK_LT:      ins->op = IR_LT;  break;
                case TOK_GT:      ins->op = IR_GT;  break;
                case TOK_LTE:     ins->op = IR_LTE; break;
                case TOK_GTE:     ins->op = IR_GTE; break;
                case TOK_AND:     ins->op = IR_BOOL_AND; break;
                case TOK_OR:      ins->op = IR_BOOL_OR;  break;
                default:          ins->op = IR_ADD; break;
            }

            ins->dst = dst;
            ins->src1 = lv;
            ins->src2 = rv;

            return dst;
        }

        case AST_UNOP: {
            IRVal ov = lower_expr(l, n->unop.operand);

            dst = ir_new_reg(b, n->resolved_type ? n->resolved_type : TY_I64_T);
            ins = ir_emit(b);

            switch (n->unop.op) {
                case TOK_MINUS:
                    ins->op = IR_NEG;
                    break;

                case TOK_BANG:
                    ins->op = IR_NOT;
                    break;

                case TOK_TILDE:
                    ins->op = IR_XOR;
                    ins->src2 = ir_const_int(-1, TY_I64_T);
                    break;

                case TOK_INC: {
                    IRVal one = ir_const_int(1, TY_I64_T);
                    IRVal sum = ir_new_reg(b, TY_I64_T);

                    IRInstr *add = ir_emit(b);
                    add->op = IR_ADD;
                    add->dst = sum;
                    add->src1 = ov;
                    add->src2 = one;

                    if (n->unop.operand->kind == AST_IDENT) {
                        IRVal addr;

                        if (irscope_get(l->scope, n->unop.operand->ident, &addr)) {
                            IRInstr *st = ir_emit(b);
                            st->op = IR_STORE;
                            st->src1 = addr;
                            st->src2 = sum;
                        }
                    }

                    ins->op = IR_ADD;
                    ins->dst = dst;
                    ins->src1 = n->unop.postfix ? ov : sum;
                    ins->src2 = ir_const_int(0, TY_I64_T);

                    return dst;
                }

                case TOK_DEC: {
                    IRVal one = ir_const_int(1, TY_I64_T);
                    IRVal diff = ir_new_reg(b, TY_I64_T);

                    IRInstr *sub = ir_emit(b);
                    sub->op = IR_SUB;
                    sub->dst = diff;
                    sub->src1 = ov;
                    sub->src2 = one;

                    if (n->unop.operand->kind == AST_IDENT) {
                        IRVal addr;

                        if (irscope_get(l->scope, n->unop.operand->ident, &addr)) {
                            IRInstr *st = ir_emit(b);
                            st->op = IR_STORE;
                            st->src1 = addr;
                            st->src2 = diff;
                        }
                    }

                    ins->op = IR_ADD;
                    ins->dst = dst;
                    ins->src1 = n->unop.postfix ? ov : diff;
                    ins->src2 = ir_const_int(0, TY_I64_T);

                    return dst;
                }

                default:
                    ins->op = IR_ADD;
                    break;
            }

            ins->dst = dst;
            ins->src1 = ov;

            return dst;
        }

        case AST_ADDR: {
            if (n->unop.operand->kind == AST_IDENT) {
                IRVal addr;

                if (irscope_get(l->scope, n->unop.operand->ident, &addr)) {
                    dst = ir_new_reg(b, type_ptr(n->unop.operand->resolved_type));

                    ins = ir_emit(b);
                    ins->op = IR_LOAD_ADDR;
                    ins->dst = dst;
                    ins->src1 = addr;

                    return dst;
                }
            }

            return lower_expr(l, n->unop.operand);
        }

        case AST_DEREF: {
            IRVal pv = lower_expr(l, n->unop.operand);

            dst = ir_new_reg(b, n->resolved_type ? n->resolved_type : TY_I64_T);

            ins = ir_emit(b);
            ins->op = IR_DEREF;
            ins->dst = dst;
            ins->src1 = pv;

            return dst;
        }

        case AST_ALLOC: {
            IRVal sz_v = lower_expr(l, n->alloc.size_expr);
            u32 tsz = type_size(n->alloc.type);
            IRVal tsz_v = ir_const_int(tsz, TY_U64_T);
            IRVal total = ir_new_reg(b, TY_U64_T);
            IRInstr *mi;

            ins = ir_emit(b);
            ins->op = IR_MUL;
            ins->dst = total;
            ins->src1 = sz_v;
            ins->src2 = tsz_v;

            dst = ir_new_reg(b, n->resolved_type ? n->resolved_type : type_ptr(TY_VOID_T));

            mi = ir_emit(b);
            mi->op = IR_MALLOC;
            mi->dst = dst;
            mi->src1 = total;

            return dst;
        }

        case AST_CAST: {
            IRVal cv = lower_expr(l, n->cast.expr);

            dst = ir_new_reg(b, n->cast.to_type);

            ins = ir_emit(b);
            ins->op = IR_CAST;
            ins->dst = dst;
            ins->src1 = cv;
            ins->cast_type = n->cast.to_type;

            return dst;
        }

        case AST_SIZEOF:
            return ir_const_int(type_size(n->sizeof_type), TY_U64_T);

        case AST_CALL: {
            int i;
            IRVal *args = (IRVal*)arena_alloc(b->arena, sizeof(IRVal) * n->call.arg_count);

            for (i = 0; i < n->call.arg_count; i++) {
                args[i] = lower_expr(l, n->call.args[i]);
            }

            dst = ir_new_reg(b, n->resolved_type ? n->resolved_type : TY_VOID_T);

            ins = ir_emit(b);
            ins->op = IR_CALL;
            ins->dst = dst;

            ins->fn_name = (n->call.callee->kind == AST_IDENT) ? n->call.callee->ident : NULL;
            ins->arg_count = n->call.arg_count;
            ins->args = args;

            return dst;
        }

        case AST_SYSCALL: {
            int i;
            int ac = n->call.arg_count;

            IRVal *args = (IRVal*)arena_alloc(b->arena, sizeof(IRVal) * (ac > 0 ? ac : 1));

            for (i = 0; i < ac; i++) {
                args[i] = lower_expr(l, n->call.args[i]);
            }

            dst = ir_new_reg(b, TY_I64_T);

            ins = ir_emit(b);
            ins->op = IR_SYSCALL;
            ins->dst = dst;
            ins->arg_count = ac;
            ins->args = args;

            return dst;
        }

        case AST_INDEX: {
            IRVal av = lower_expr(l, n->index.array);
            IRVal iv = lower_expr(l, n->index.index);
            u32 esz = n->resolved_type ? type_size(n->resolved_type) : 8;
            IRVal esz_v = ir_const_int(esz, TY_U64_T);

            IRVal off = ir_new_reg(b, TY_U64_T);
            IRVal ptr;

            ins = ir_emit(b);
            ins->op = IR_MUL;
            ins->dst = off;
            ins->src1 = iv;
            ins->src2 = esz_v;

            ptr = ir_new_reg(b, type_ptr(n->resolved_type ? n->resolved_type : TY_U8_T));

            {
                IRInstr *ai = ir_emit(b);
                ai->op = IR_ADD;
                ai->dst = ptr;
                ai->src1 = av;
                ai->src2 = off;
            }

            dst = ir_new_reg(b, n->resolved_type ? n->resolved_type : TY_U8_T);

            {
                IRInstr *ld = ir_emit(b);
                ld->op = IR_DEREF;
                ld->dst = dst;
                ld->src1 = ptr;
            }

            return dst;
        }

        case AST_FIELD: {
            IRVal ov = lower_expr(l, n->field.object);
            Type *ot = n->field.object->resolved_type;
            u32 offset = 0;

            if (ot && ot->kind == TY_STRUCT) {
                offset = type_field_offset(ot, n->field.field);
            }

            dst = ir_new_reg(b, n->resolved_type ? n->resolved_type : TY_U64_T);

            ins = ir_emit(b);
            ins->op = IR_FIELD_PTR;
            ins->dst = dst;
            ins->src1 = ov;
            ins->field_idx = offset;

            return dst;
        }

        case AST_ARROW: {
            IRVal pv = lower_expr(l, n->arrow.ptr);
            Type *pt = n->arrow.ptr->resolved_type;
            Type *st = (pt && pt->kind == TY_PTR) ? pt->base : pt;
            u32 offset = 0;

            if (st && st->kind == TY_STRUCT) {
                offset = type_field_offset(st, n->arrow.field);
            }

            dst = ir_new_reg(b, n->resolved_type ? n->resolved_type : TY_U64_T);

            ins = ir_emit(b);
            ins->op = IR_FIELD_PTR;
            ins->dst = dst;
            ins->src1 = pv;
            ins->field_idx = offset;

            return dst;
        }

        case AST_ASSIGN_EXPR: {
            IRVal rv = lower_expr(l, n->assign.value);

            if (n->assign.target->kind == AST_IDENT) {
                IRVal addr;

                if (irscope_get(l->scope, n->assign.target->ident, &addr)) {
                    if (n->assign.op != TOK_ASSIGN) {
                        IRVal cur = ir_new_reg(b, n->resolved_type ? n->resolved_type : TY_I64_T);
                        IRVal res = ir_new_reg(b, n->resolved_type ? n->resolved_type : TY_I64_T);

                        IRInstr *ld = ir_emit(b);
                        IRInstr *op = ir_emit(b);
                        IRInstr *st = ir_emit(b);

                        ld->op = IR_DEREF;
                        ld->dst = cur;
                        ld->src1 = addr;

                        switch (n->assign.op) {
                            case TOK_PLUS_ASSIGN:  op->op = IR_ADD; break;
                            case TOK_MINUS_ASSIGN: op->op = IR_SUB; break;
                            case TOK_STAR_ASSIGN:  op->op = IR_MUL; break;
                            case TOK_SLASH_ASSIGN: op->op = IR_DIV; break;
                            default:               op->op = IR_ADD; break;
                        }

                        op->dst = res;
                        op->src1 = cur;
                        op->src2 = rv;

                        st->op = IR_STORE;
                        st->src1 = addr;
                        st->src2 = res;

                        return res;
                    } else {
                        IRInstr *st = ir_emit(b);
                        st->op = IR_STORE;
                        st->src1 = addr;
                        st->src2 = rv;
                    }
                } else {
                    ins = ir_emit(b);
                    ins->op = IR_STORE;
                    ins->label = n->assign.target->ident;
                    ins->src2 = rv;
                }
            } else if (n->assign.target->kind == AST_DEREF) {
                IRVal pv = lower_expr(l, n->assign.target->unop.operand);

                ins = ir_emit(b);
                ins->op = IR_STORE;
                ins->src1 = pv;
                ins->src2 = rv;
            } else if (n->assign.target->kind == AST_INDEX) {
                IRVal av = lower_expr(l, n->assign.target->index.array);
                IRVal iv = lower_expr(l, n->assign.target->index.index);
                u32 esz = rv.type ? type_size(rv.type) : 8;
                IRVal esz_v = ir_const_int(esz, TY_U64_T);

                IRVal off = ir_new_reg(b, TY_U64_T);
                IRVal ptr;

                IRInstr *mi = ir_emit(b);
                IRInstr *ai = ir_emit(b);

                mi->op = IR_MUL;
                mi->dst = off;
                mi->src1 = iv;
                mi->src2 = esz_v;

                ptr = ir_new_reg(b, type_ptr(TY_U8_T));

                ai->op = IR_ADD;
                ai->dst = ptr;
                ai->src1 = av;
                ai->src2 = off;

                ins = ir_emit(b);
                ins->op = IR_STORE;
                ins->src1 = ptr;
                ins->src2 = rv;
            }

            return rv;
        }

        default:
            return IRVAL_NONE_V;
    }
}

static void lower_stmt(IRLower *l, ASTNode *n) {
    IRBuilder *b = l->b;
    IRInstr   *ins;

    if (!n) return;

    switch (n->kind) {
        case AST_BLOCK: {
            int i;
            IRScope *old = l->scope;

            l->scope = irscope_new(b->arena, old);

            for (i = 0; i < n->block.count; i++) {
                lower_stmt(l, n->block.stmts[i]);
            }

            l->scope = old;
            return;
        }

        case AST_VAR_DECL: {
            IRVal addr = ir_new_reg(b, type_ptr(n->var_decl.type));

            ins = ir_emit(b);
            ins->op = IR_ALLOCA;
            ins->dst = addr;
            ins->alloc_type = n->var_decl.type;

            irscope_set(l->scope, n->var_decl.name, addr);

            if (n->var_decl.init) {
                IRVal iv = lower_expr(l, n->var_decl.init);

                IRInstr *st = ir_emit(b);
                st->op = IR_STORE;
                st->src1 = addr;
                st->src2 = iv;
            }

            return;
        }

        case AST_EXPR_STMT:
            lower_expr(l, n->unop.operand);
            return;

        case AST_ASSIGN_EXPR:
            lower_expr(l, n);
            return;

        case AST_PRINT_VAR:
        case AST_PRINT_EXPR: {
            IRVal v = lower_expr(l, n->unop.operand);
            Type *t = v.type ? v.type : TY_I64_T;

            ins = ir_emit(b);

            if (type_is_float(t)) {
                ins->op = IR_PRINT_FLOAT;
            } else if (t->kind == TY_PTR && t->base && t->base->kind == TY_CHAR) {
                ins->op = IR_PRINT_STR;
            } else {
                ins->op = IR_PRINT_INT;
            }

            ins->src1 = v;
            return;
        }

        case AST_PRINT_STR: {
            ins = ir_emit(b);
            ins->op = IR_PRINT_STR;
            ins->src1 = ir_str_val(n->str_val);
            return;
        }

        case AST_RETURN: {
            IRVal rv = n->ret.value ? lower_expr(l, n->ret.value) : IRVAL_NONE_V;

            ins = ir_emit(b);
            ins->op = IR_RET;
            ins->src1 = rv;

            return;
        }

        case AST_IF: {
            IRVal cv = lower_expr(l, n->if_stmt.cond);
            char *lend = ir_new_label(b, "if_end");
            char *lnext = ir_new_label(b, "if_else");
            int i;

            ins = ir_emit(b);
            ins->op = IR_JZ;
            ins->src1 = cv;
            ins->label = lnext;

            lower_stmt(l, n->if_stmt.then_block);

            {
                IRInstr *j = ir_emit(b);
                j->op = IR_JMP;
                j->label = lend;
            }

            for (i = 0; i < n->if_stmt.elif_count; i++) {
                IRInstr *lbl = ir_emit(b);
                IRInstr *jz;
                IRInstr *j;
                IRVal ecv;

                lbl->op = IR_LABEL;
                lbl->label = lnext;

                lnext = ir_new_label(b, "elif_next");

                ecv = lower_expr(l, n->if_stmt.elif_conds[i]);

                jz = ir_emit(b);
                jz->op = IR_JZ;
                jz->src1 = ecv;
                jz->label = lnext;

                lower_stmt(l, n->if_stmt.elif_blocks[i]);

                j = ir_emit(b);
                j->op = IR_JMP;
                j->label = lend;
            }

            {
                IRInstr *lbl = ir_emit(b);
                lbl->op = IR_LABEL;
                lbl->label = lnext;
            }

            if (n->if_stmt.else_block) lower_stmt(l, n->if_stmt.else_block);

            {
                IRInstr *lbl = ir_emit(b);
                lbl->op = IR_LABEL;
                lbl->label = lend;
            }

            return;
        }

        case AST_LOOP: {
            char *lcond = ir_new_label(b, "lp_cond");
            char *lend = ir_new_label(b, "lp_end");
            IRVal cv;

            {
                IRInstr *lbl = ir_emit(b);
                lbl->op = IR_LABEL;
                lbl->label = lcond;
            }

            cv = lower_expr(l, n->loop.cond);

            ins = ir_emit(b);
            ins->op = IR_JZ;
            ins->src1 = cv;
            ins->label = lend;

            lower_push_loop(l, lend, lcond);
            lower_stmt(l, n->loop.body);
            lower_pop_loop(l);

            {
                IRInstr *j = ir_emit(b);
                j->op = IR_JMP;
                j->label = lcond;
            }

            {
                IRInstr *lbl = ir_emit(b);
                lbl->op = IR_LABEL;
                lbl->label = lend;
            }

            return;
        }

        case AST_FOR: {
            char *lcond = ir_new_label(b, "fr_cond");
            char *lpost = ir_new_label(b, "fr_post");
            char *lend = ir_new_label(b, "fr_end");
            IRScope *old = l->scope;
            IRVal cv;

            l->scope = irscope_new(b->arena, old);

            lower_stmt(l, n->for_stmt.init);

            {
                IRInstr *lbl = ir_emit(b);
                lbl->op = IR_LABEL;
                lbl->label = lcond;
            }

            cv = lower_expr(l, n->for_stmt.cond);

            ins = ir_emit(b);
            ins->op = IR_JZ;
            ins->src1 = cv;
            ins->label = lend;

            lower_push_loop(l, lend, lpost);
            lower_stmt(l, n->for_stmt.body);
            lower_pop_loop(l);

            {
                IRInstr *lbl = ir_emit(b);
                lbl->op = IR_LABEL;
                lbl->label = lpost;
            }

            lower_expr(l, n->for_stmt.post);

            {
                IRInstr *j = ir_emit(b);
                j->op = IR_JMP;
                j->label = lcond;
            }

            {
                IRInstr *lbl = ir_emit(b);
                lbl->op = IR_LABEL;
                lbl->label = lend;
            }

            l->scope = old;
            return;
        }

        case AST_BREAK: {
            char *lbl = lower_current_break(l);

            if (!lbl) {
                FATAL(n->line, n->col, "BK outside loop");
            }

            ins = ir_emit(b);
            ins->op = IR_JMP;
            ins->label = lbl;

            return;
        }

        case AST_SKIP: {
            char *lbl = lower_current_cont(l);

            if (!lbl) {
                FATAL(n->line, n->col, "SK outside loop");
            }

            ins = ir_emit(b);
            ins->op = IR_JMP;
            ins->label = lbl;

            return;
        }

        case AST_FN_DECL: {
            int i;
            IRScope *old = l->scope;

            ins = ir_emit(b);
            ins->op = IR_FN_BEGIN;
            ins->fn_name = n->fn_decl.name;

            l->scope = irscope_new(b->arena, old);

            for (i = 0; i < n->fn_decl.param_count; i++) {
                IRVal preg = ir_new_reg(b, n->fn_decl.param_types[i]);

                IRInstr *pi = ir_emit(b);
                pi->op = IR_PARAM;
                pi->dst = preg;
                pi->label = n->fn_decl.param_names[i];
                pi->alloc_type = n->fn_decl.param_types[i];
                pi->field_idx = (u32)i;

                {
                    IRVal addr = ir_new_reg(b, type_ptr(n->fn_decl.param_types[i]));

                    IRInstr *al = ir_emit(b);
                    al->op = IR_ALLOCA;
                    al->dst = addr;
                    al->alloc_type = n->fn_decl.param_types[i];

                    IRInstr *st = ir_emit(b);
                    st->op = IR_STORE;
                    st->src1 = addr;
                    st->src2 = preg;

                    irscope_set(l->scope, n->fn_decl.param_names[i], addr);
                }
            }

            lower_stmt(l, n->fn_decl.body);

            l->scope = old;

            {
                IRInstr *end = ir_emit(b);
                end->op = IR_FN_END;
                end->fn_name = n->fn_decl.name;
            }

            return;
        }

        case AST_STRUCT_DECL:
            return;

        case AST_IMPORT:
            return;

        case AST_INLINE_ASM:
            FATAL(n->line, n->col, "ASM is disabled; use SC(...) for syscalls");
            return;

        case AST_FREE: {
            IRVal pv = lower_expr(l, n->free_stmt.expr);

            ins = ir_emit(b);
            ins->op = IR_FREE;
            ins->src1 = pv;

            return;
        }

        default:
            return;
    }
}

typedef struct {
    u8  *buf;
    u32  pos;
    u32  cap;

    struct { u32 offset; char *label; u8 type; } *relocs;
    u32  reloc_count;
    u32  reloc_cap;

    struct { char *name; u32 offset; } *labels;
    u32  label_count;
    u32  label_cap;

    i32 *vreg_slots;
    u32  vreg_count;
    i32  stack_top;

    struct { char *str; u32 offset; } *strings;
    u32  str_count;
    u32  str_cap;

    u32 *frame_patches;
    u32  frame_count;
    u32  frame_cap;

    Arena *arena;
} X64Ctx;

#define REG_RAX 0
#define REG_RCX 1
#define REG_RDX 2
#define REG_RBX 3
#define REG_RSP 4
#define REG_RBP 5
#define REG_RSI 6
#define REG_RDI 7
#define REG_R8  8
#define REG_R9  9
#define REG_R10 10
#define REG_R11 11

#define MODRM(mod,reg,rm) (((mod)<<6)|((reg&7)<<3)|(rm&7))

static const u8 CALL_ARG_REGS[6]   = { REG_RDI, REG_RSI, REG_RDX, REG_RCX, REG_R8, REG_R9 };
static const u8 SYSCALL_ARG_REGS[7] = { REG_RAX, REG_RDI, REG_RSI, REG_RDX, REG_R10, REG_R8, REG_R9 };

static void x64_init(X64Ctx *c, Arena *a) {
    c->cap = 64 * 1024;
    c->buf = (u8*)malloc(c->cap);
    c->pos = 0;

    c->relocs = NULL;
    c->reloc_count = c->reloc_cap = 0;

    c->labels = NULL;
    c->label_count = c->label_cap = 0;

    c->vreg_slots = NULL;
    c->vreg_count = 0;
    c->stack_top = 0;

    c->strings = NULL;
    c->str_count = c->str_cap = 0;

    c->frame_patches = NULL;
    c->frame_count = c->frame_cap = 0;

    c->arena = a;
}

static void x64_grow(X64Ctx *c, u32 need) {
    while (c->pos + need > c->cap) {
        c->cap *= 2;
        c->buf = (u8*)realloc(c->buf, c->cap);
    }
}

static void x64_emit(X64Ctx *c, u8 byte) {
    x64_grow(c, 1);
    c->buf[c->pos++] = byte;
}

static void x64_emit2(X64Ctx *c, u8 a, u8 b) {
    x64_emit(c, a);
    x64_emit(c, b);
}

static void x64_emit32(X64Ctx *c, u32 v) {
    x64_grow(c, 4);

    c->buf[c->pos + 0] = (u8)(v);
    c->buf[c->pos + 1] = (u8)(v >> 8);
    c->buf[c->pos + 2] = (u8)(v >> 16);
    c->buf[c->pos + 3] = (u8)(v >> 24);

    c->pos += 4;
}

static void x64_emit64(X64Ctx *c, u64 v) {
    x64_grow(c, 8);

    c->buf[c->pos + 0] = (u8)(v);
    c->buf[c->pos + 1] = (u8)(v >> 8);
    c->buf[c->pos + 2] = (u8)(v >> 16);
    c->buf[c->pos + 3] = (u8)(v >> 24);
    c->buf[c->pos + 4] = (u8)(v >> 32);
    c->buf[c->pos + 5] = (u8)(v >> 40);
    c->buf[c->pos + 6] = (u8)(v >> 48);
    c->buf[c->pos + 7] = (u8)(v >> 56);

    c->pos += 8;
}

static void x64_patch32(X64Ctx *c, u32 at, u32 val) {
    c->buf[at + 0] = (u8)(val);
    c->buf[at + 1] = (u8)(val >> 8);
    c->buf[at + 2] = (u8)(val >> 16);
    c->buf[at + 3] = (u8)(val >> 24);
}

static void x64_define_label(X64Ctx *c, const char *name) {
    if (c->label_count >= c->label_cap) {
        c->label_cap = c->label_cap ? c->label_cap * 2 : 64;
        c->labels = realloc(c->labels, c->label_cap * sizeof(*c->labels));
    }

    c->labels[c->label_count].name = arena_strdup(c->arena, name);
    c->labels[c->label_count].offset = c->pos;
    c->label_count++;
}

static u32 x64_find_label(X64Ctx *c, const char *name) {
    u32 i;

    for (i = 0; i < c->label_count; i++) {
        if (strcmp(c->labels[i].name, name) == 0) {
            return c->labels[i].offset;
        }
    }

    return 0xFFFFFFFF;
}

static void x64_add_reloc(X64Ctx *c, u32 offset, const char *label) {
    if (c->reloc_count >= c->reloc_cap) {
        c->reloc_cap = c->reloc_cap ? c->reloc_cap * 2 : 64;
        c->relocs = realloc(c->relocs, c->reloc_cap * sizeof(*c->relocs));
    }

    c->relocs[c->reloc_count].offset = offset;
    c->relocs[c->reloc_count].label = arena_strdup(c->arena, label);
    c->relocs[c->reloc_count].type = 0;
    c->reloc_count++;
}

static void x64_rr(X64Ctx *c, u8 op, u8 dst, u8 src) {
    u8 rex = 0x48;

    if (dst >= 8) rex |= 0x04;
    if (src >= 8) rex |= 0x01;

    x64_emit(c, rex);
    x64_emit(c, op);
    x64_emit(c, MODRM(3, dst & 7, src & 7));
}

static void x64_mov_rr(X64Ctx *c, u8 dst, u8 src) {
    x64_rr(c, 0x8B, dst, src);
}

static void x64_mov_ri64(X64Ctx *c, u8 reg, u64 imm) {
    u8 rex = 0x48;

    if (reg >= 8) rex |= 0x01;

    x64_emit(c, rex);
    x64_emit(c, 0xB8 | (reg & 7));
    x64_emit64(c, imm);
}

static void x64_mov_mem_reg(X64Ctx *c, i32 off, u8 reg) {
    u8 rex = 0x48;

    if (reg >= 8) rex |= 0x04;

    x64_emit(c, rex);
    x64_emit(c, 0x89);

    if (off >= -128 && off <= 127) {
        x64_emit(c, MODRM(1, reg & 7, REG_RBP));
        x64_emit(c, (u8)(i8)off);
    } else {
        x64_emit(c, MODRM(2, reg & 7, REG_RBP));
        x64_emit32(c, (u32)off);
    }
}

static void x64_mov_reg_mem(X64Ctx *c, u8 reg, i32 off) {
    u8 rex = 0x48;

    if (reg >= 8) rex |= 0x04;

    x64_emit(c, rex);
    x64_emit(c, 0x8B);

    if (off >= -128 && off <= 127) {
        x64_emit(c, MODRM(1, reg & 7, REG_RBP));
        x64_emit(c, (u8)(i8)off);
    } else {
        x64_emit(c, MODRM(2, reg & 7, REG_RBP));
        x64_emit32(c, (u32)off);
    }
}

static void x64_push(X64Ctx *c, u8 reg) {
    if (reg >= 8) x64_emit(c, 0x41);
    x64_emit(c, 0x50 | (reg & 7));
}

static void x64_pop(X64Ctx *c, u8 reg) {
    if (reg >= 8) x64_emit(c, 0x41);
    x64_emit(c, 0x58 | (reg & 7));
}

static void x64_sub_rsp(X64Ctx *c, u32 n) {
    x64_emit(c, 0x48);
    x64_emit(c, 0x81);
    x64_emit(c, 0xEC);
    x64_emit32(c, n);
}

static void x64_add_rsp(X64Ctx *c, u32 n) {
    x64_emit(c, 0x48);
    x64_emit(c, 0x81);
    x64_emit(c, 0xC4);
    x64_emit32(c, n);
}

static void x64_ret(X64Ctx *c) {
    x64_emit(c, 0xC3);
}

static void x64_cmp_rr(X64Ctx *c, u8 r1, u8 r2) {
    x64_rr(c, 0x3B, r1, r2);
}

static void x64_test_rr(X64Ctx *c, u8 r1, u8 r2) {
    x64_rr(c, 0x85, r1, r2);
}

static void x64_sete(X64Ctx *c) {
    x64_emit2(c, 0x0F, 0x94);
    x64_emit(c, 0xC0);
}

static void x64_setne(X64Ctx *c) {
    x64_emit2(c, 0x0F, 0x95);
    x64_emit(c, 0xC0);
}

static void x64_setl(X64Ctx *c) {
    x64_emit2(c, 0x0F, 0x9C);
    x64_emit(c, 0xC0);
}

static void x64_setg(X64Ctx *c) {
    x64_emit2(c, 0x0F, 0x9F);
    x64_emit(c, 0xC0);
}

static void x64_setle(X64Ctx *c) {
    x64_emit2(c, 0x0F, 0x9E);
    x64_emit(c, 0xC0);
}

static void x64_setge(X64Ctx *c) {
    x64_emit2(c, 0x0F, 0x9D);
    x64_emit(c, 0xC0);
}

static void x64_movzx_rax_al(X64Ctx *c) {
    x64_emit(c, 0x48);
    x64_emit(c, 0x0F);
    x64_emit(c, 0xB6);
    x64_emit(c, 0xC0);
}

static void x64_idiv(X64Ctx *c, u8 reg) {
    u8 rex = 0x48;

    if (reg >= 8) rex |= 0x01;

    x64_emit(c, rex);
    x64_emit(c, 0xF7);
    x64_emit(c, 0xF8 | (reg & 7));
}

static void x64_cqo(X64Ctx *c) {
    x64_emit(c, 0x48);
    x64_emit(c, 0x99);
}

static void x64_xor_rr(X64Ctx *c, u8 dst, u8 src) {
    x64_rr(c, 0x33, dst, src);
}

static void x64_add_rr(X64Ctx *c, u8 dst, u8 src) {
    x64_rr(c, 0x03, dst, src);
}

static void x64_sub_rr(X64Ctx *c, u8 dst, u8 src) {
    x64_rr(c, 0x2B, dst, src);
}

static void x64_and_rr(X64Ctx *c, u8 dst, u8 src) {
    x64_rr(c, 0x23, dst, src);
}

static void x64_or_rr(X64Ctx *c, u8 dst, u8 src) {
    x64_rr(c, 0x0B, dst, src);
}

static void x64_neg(X64Ctx *c, u8 reg) {
    u8 rex = 0x48;

    if (reg >= 8) rex |= 0x01;

    x64_emit(c, rex);
    x64_emit(c, 0xF7);
    x64_emit(c, 0xD8 | (reg & 7));
}

static void x64_not(X64Ctx *c, u8 reg) {
    u8 rex = 0x48;

    if (reg >= 8) rex |= 0x01;

    x64_emit(c, rex);
    x64_emit(c, 0xF7);
    x64_emit(c, 0xD0 | (reg & 7));
}

static void x64_shl_cl(X64Ctx *c, u8 reg) {
    u8 rex = 0x48;

    if (reg >= 8) rex |= 0x01;

    x64_emit(c, rex);
    x64_emit(c, 0xD3);
    x64_emit(c, 0xE0 | (reg & 7));
}

static void x64_shr_cl(X64Ctx *c, u8 reg) {
    u8 rex = 0x48;

    if (reg >= 8) rex |= 0x01;

    x64_emit(c, rex);
    x64_emit(c, 0xD3);
    x64_emit(c, 0xE8 | (reg & 7));
}

static void x64_store_ptr(X64Ctx *c, u8 ptr_reg, u8 val_reg, u32 sz) {
    u8 rex = 0x48;

    if (ptr_reg >= 8) rex |= 0x01;
    if (val_reg >= 8) rex |= 0x04;

    if (sz == 8) {
        x64_emit(c, rex);
        x64_emit(c, 0x89);
        x64_emit(c, MODRM(0, val_reg & 7, ptr_reg & 7));
    } else if (sz == 4) {
        x64_emit(c, 0x89);
        x64_emit(c, MODRM(0, val_reg & 7, ptr_reg & 7));
    } else if (sz == 1) {
        x64_emit(c, 0x88);
        x64_emit(c, MODRM(0, val_reg & 7, ptr_reg & 7));
    }
}

static void x64_load_ptr(X64Ctx *c, u8 dst_reg, u8 ptr_reg, u32 sz) {
    u8 rex = 0x48;

    if (dst_reg >= 8) rex |= 0x04;
    if (ptr_reg >= 8) rex |= 0x01;

    if (sz == 8) {
        x64_emit(c, rex);
        x64_emit(c, 0x8B);
        x64_emit(c, MODRM(0, dst_reg & 7, ptr_reg & 7));
    } else if (sz == 4) {
        x64_emit(c, 0x8B);
        x64_emit(c, MODRM(0, dst_reg & 7, ptr_reg & 7));
    } else if (sz == 1) {
        x64_emit2(c, 0x0F, 0xB6);
        x64_emit(c, MODRM(0, dst_reg & 7, ptr_reg & 7));
    }
}

static void x64_syscall(X64Ctx *c) {
    x64_emit2(c, 0x0F, 0x05);
}

static i32 x64_vreg_slot(X64Ctx *c, u32 vreg) {
    if (vreg >= c->vreg_count) {
        u32 newcnt = vreg + 64;
        u32 i;

        c->vreg_slots = (i32*)realloc(c->vreg_slots, sizeof(i32) * newcnt);

        for (i = c->vreg_count; i < newcnt; i++) {
            c->vreg_slots[i] = 0;
        }

        c->vreg_count = newcnt;
    }

    if (c->vreg_slots[vreg] == 0) {
        c->stack_top -= 8;
        c->vreg_slots[vreg] = c->stack_top;
    }

    return c->vreg_slots[vreg];
}

static void x64_load_vreg(X64Ctx *c, u8 phys, IRVal v) {
    if (v.kind == IRVAL_CONST_INT) {
        x64_mov_ri64(c, phys, (u64)v.ival);
    } else if (v.kind == IRVAL_REG) {
        i32 slot = x64_vreg_slot(c, v.reg);
        x64_mov_reg_mem(c, phys, slot);
    } else if (v.kind == IRVAL_NONE) {
        x64_xor_rr(c, phys, phys);
    }
}

static void x64_store_vreg(X64Ctx *c, IRVal dst, u8 phys) {
    i32 slot = x64_vreg_slot(c, dst.reg);
    x64_mov_mem_reg(c, slot, phys);
}

static u32 x64_add_string(X64Ctx *c, const char *s) {
    u32 i;

    for (i = 0; i < c->str_count; i++) {
        if (strcmp(c->strings[i].str, s) == 0) {
            return i;
        }
    }

    if (c->str_count >= c->str_cap) {
        c->str_cap = c->str_cap ? c->str_cap * 2 : 16;
        c->strings = realloc(c->strings, c->str_cap * sizeof(*c->strings));
    }

    c->strings[c->str_count].str = arena_strdup(c->arena, s);
    c->strings[c->str_count].offset = 0;

    return c->str_count++;
}

static void x64_emit_runtime_helpers(X64Ctx *c) {
    x64_define_label(c, "_forge_print_str");

    x64_push(c, REG_RSI);
    x64_push(c, REG_RDX);

    x64_mov_ri64(c, REG_RAX, 1);
    x64_mov_ri64(c, REG_RDI, 1);

    x64_pop(c, REG_RDX);
    x64_pop(c, REG_RSI);

    x64_syscall(c);
    x64_ret(c);

    x64_define_label(c, "_forge_print_int");

    x64_sub_rsp(c, 40);
    x64_mov_rr(c, REG_RAX, REG_RDI);

    x64_emit(c, 0x4C);
    x64_emit(c, 0x8D);
    x64_emit(c, 0x44);
    x64_emit(c, 0x24);
    x64_emit(c, 31);

    x64_xor_rr(c, REG_R9, REG_R9);
    x64_test_rr(c, REG_RAX, REG_RAX);

    x64_emit(c, 0x0F);
    x64_emit(c, 0x89);

    {
        u32 jge_patch = c->pos;
        u32 here;

        x64_emit32(c, 0);

        x64_neg(c, REG_RAX);
        x64_mov_ri64(c, REG_R9, 1);

        here = c->pos;
        x64_patch32(c, jge_patch, here - jge_patch - 4);
    }

    x64_define_label(c, "_forge_print_int_loop");

    x64_xor_rr(c, REG_RDX, REG_RDX);

    x64_emit(c, 0x48);
    x64_emit(c, 0xC7);
    x64_emit(c, 0xC1);
    x64_emit32(c, 10);

    x64_idiv(c, REG_RCX);

    x64_emit(c, 0x80);
    x64_emit(c, 0xC2);
    x64_emit(c, '0');

    x64_emit(c, 0x49);
    x64_emit(c, 0xFF);
    x64_emit(c, 0xC8);

    x64_emit(c, 0x41);
    x64_emit(c, 0x88);
    x64_emit(c, 0x10);

    x64_test_rr(c, REG_RAX, REG_RAX);

    x64_emit(c, 0x0F);
    x64_emit(c, 0x85);

    {
        u32 jnz_patch = c->pos;
        u32 here;

        x64_emit32(c, 0);

        here = c->pos;
        x64_patch32(c, jnz_patch, here - jnz_patch - 4);
    }

    x64_test_rr(c, REG_R9, REG_R9);

    x64_emit(c, 0x0F);
    x64_emit(c, 0x84);

    {
        u32 jz_patch = c->pos;
        u32 here;

        x64_emit32(c, 0);

        x64_emit(c, 0x49);
        x64_emit(c, 0xFF);
        x64_emit(c, 0xC8);

        x64_emit(c, 0x41);
        x64_emit(c, 0xC6);
        x64_emit(c, 0x00);
        x64_emit(c, '-');

        here = c->pos;
        x64_patch32(c, jz_patch, here - jz_patch - 4);
    }

    x64_emit(c, 0x48);
    x64_emit(c, 0x8D);
    x64_emit(c, 0x54);
    x64_emit(c, 0x24);
    x64_emit(c, 32);

    x64_sub_rr(c, REG_RDX, REG_R8);
    x64_mov_rr(c, REG_RSI, REG_R8);

    x64_mov_ri64(c, REG_RAX, 1);
    x64_mov_ri64(c, REG_RDI, 1);

    x64_syscall(c);

    x64_add_rsp(c, 40);
    x64_ret(c);
}

static void x64_codegen(X64Ctx *c, IRBuilder *b) {
    u32 i;

    typedef struct {
        char *name;
        u32   site;
    } JmpPatch;

    JmpPatch *patches = (JmpPatch*)malloc(sizeof(JmpPatch) * 1024);
    u32 patch_count = 0;

    for (i = 0; i < b->count; i++) {
        IRInstr *ins = &b->instrs[i];

        switch (ins->op) {
            case IR_NOP:
                break;

            case IR_LABEL:
                x64_define_label(c, ins->label);
                break;

            case IR_FN_BEGIN: {
                x64_define_label(c, ins->fn_name);

                x64_push(c, REG_RBP);

                x64_emit(c, 0x48);
                x64_emit(c, 0x89);
                x64_emit(c, 0xE5);

                x64_emit(c, 0x48);
                x64_emit(c, 0x81);
                x64_emit(c, 0xEC);

                if (c->frame_count >= c->frame_cap) {
                    c->frame_cap = c->frame_cap ? c->frame_cap * 2 : 32;
                    c->frame_patches = (u32*)realloc(c->frame_patches, sizeof(u32) * c->frame_cap);
                }

                c->frame_patches[c->frame_count++] = c->pos;
                x64_emit32(c, 0x100);

                c->stack_top = 0;

                {
                    u32 j;

                    for (j = 0; j < c->vreg_count; j++) {
                        c->vreg_slots[j] = 0;
                    }
                }

                break;
            }

            case IR_FN_END: {
                if (c->frame_count > 0) {
                    u32 fp = c->frame_patches[--c->frame_count];
                    u32 frame_sz = (u32)(-(c->stack_top));

                    frame_sz = (frame_sz + 15) & ~15u;
                    x64_patch32(c, fp, frame_sz);
                }

                x64_emit(c, 0x48);
                x64_emit(c, 0x89);
                x64_emit(c, 0xEC);

                x64_pop(c, REG_RBP);
                x64_ret(c);

                break;
            }

            case IR_PARAM: {
                u32 idx = ins->field_idx;

                if (idx < 6) {
                    x64_store_vreg(c, ins->dst, CALL_ARG_REGS[idx]);
                } else {
                    i32 off = 24 + (i32)(idx - 6) * 8;

                    x64_mov_reg_mem(c, REG_RAX, off);
                    x64_store_vreg(c, ins->dst, REG_RAX);
                }

                break;
            }

            case IR_ALLOCA: {
                u32 sz = ins->alloc_type ? type_size(ins->alloc_type) : 8;
                i32 slot;
                i32 addr_slot;

                if (sz < 8) sz = 8;

                c->stack_top -= (i32)sz;
                slot = c->stack_top;

                if (ins->dst.kind == IRVAL_REG) {
                    if (ins->dst.reg >= c->vreg_count) {
                        u32 nc = ins->dst.reg + 64;
                        u32 j;

                        c->vreg_slots = (i32*)realloc(c->vreg_slots, sizeof(i32) * nc);

                        for (j = c->vreg_count; j < nc; j++) {
                            c->vreg_slots[j] = 0;
                        }

                        c->vreg_count = nc;
                    }

                    c->vreg_slots[ins->dst.reg] = slot;

                    x64_emit(c, 0x48);
                    x64_emit(c, 0x8D);

                    if (slot >= -128 && slot <= 127) {
                        x64_emit(c, MODRM(1, REG_RAX, REG_RBP));
                        x64_emit(c, (u8)(i8)slot);
                    } else {
                        x64_emit(c, MODRM(2, REG_RAX, REG_RBP));
                        x64_emit32(c, (u32)slot);
                    }

                    c->stack_top -= 8;
                    addr_slot = c->stack_top;
                    c->vreg_slots[ins->dst.reg] = addr_slot;

                    x64_mov_mem_reg(c, addr_slot, REG_RAX);
                }

                break;
            }

            case IR_CONST_STR: {
                u32 stridx = x64_add_string(c, ins->src1.sval ? ins->src1.sval : "");

                if (ins->dst.kind == IRVAL_REG) {
                    char lbl[32];
                    i32 slot;

                    x64_emit(c, 0x48);
                    x64_emit(c, 0x8D);
                    x64_emit(c, 0x05);

                    sprintf(lbl, "__str_%u", stridx);
                    x64_add_reloc(c, c->pos, lbl);
                    x64_emit32(c, 0);

                    slot = x64_vreg_slot(c, ins->dst.reg);
                    x64_mov_mem_reg(c, slot, REG_RAX);
                }

                break;
            }

            case IR_STORE: {
                x64_load_vreg(c, REG_RAX, ins->src1);
                x64_load_vreg(c, REG_RCX, ins->src2);
                x64_store_ptr(c, REG_RAX, REG_RCX, 8);
                break;
            }

            case IR_DEREF: {
                x64_load_vreg(c, REG_RAX, ins->src1);
                x64_load_ptr(c, REG_RCX, REG_RAX, 8);
                x64_store_vreg(c, ins->dst, REG_RCX);
                break;
            }

            case IR_LOAD_ADDR: {
                x64_load_vreg(c, REG_RAX, ins->src1);
                x64_store_vreg(c, ins->dst, REG_RAX);
                break;
            }

            case IR_LOAD: {
                if (ins->dst.kind == IRVAL_REG) {
                    x64_emit(c, 0x48);
                    x64_emit(c, 0x8B);
                    x64_emit(c, 0x05);

                    x64_add_reloc(c, c->pos, ins->label ? ins->label : "?");
                    x64_emit32(c, 0);

                    x64_store_vreg(c, ins->dst, REG_RAX);
                }

                break;
            }

            case IR_ADD:
            case IR_SUB:
            case IR_AND:
            case IR_OR:
            case IR_XOR: {
                x64_load_vreg(c, REG_RAX, ins->src1);
                x64_load_vreg(c, REG_RCX, ins->src2);

                switch (ins->op) {
                    case IR_ADD: x64_add_rr(c, REG_RAX, REG_RCX); break;
                    case IR_SUB: x64_sub_rr(c, REG_RAX, REG_RCX); break;
                    case IR_AND: x64_and_rr(c, REG_RAX, REG_RCX); break;
                    case IR_OR:  x64_or_rr(c, REG_RAX, REG_RCX);  break;
                    case IR_XOR: x64_xor_rr(c, REG_RAX, REG_RCX); break;
                    default: break;
                }

                x64_store_vreg(c, ins->dst, REG_RAX);
                break;
            }

            case IR_MUL: {
                x64_load_vreg(c, REG_RAX, ins->src1);
                x64_load_vreg(c, REG_RCX, ins->src2);

                x64_emit(c, 0x48);
                x64_emit(c, 0x0F);
                x64_emit(c, 0xAF);
                x64_emit(c, MODRM(3, REG_RAX, REG_RCX));

                x64_store_vreg(c, ins->dst, REG_RAX);
                break;
            }

            case IR_DIV:
            case IR_MOD: {
                x64_load_vreg(c, REG_RAX, ins->src1);
                x64_load_vreg(c, REG_RCX, ins->src2);

                x64_cqo(c);
                x64_idiv(c, REG_RCX);

                if (ins->op == IR_DIV) {
                    x64_store_vreg(c, ins->dst, REG_RAX);
                } else {
                    x64_store_vreg(c, ins->dst, REG_RDX);
                }

                break;
            }

            case IR_NEG: {
                x64_load_vreg(c, REG_RAX, ins->src1);
                x64_neg(c, REG_RAX);
                x64_store_vreg(c, ins->dst, REG_RAX);
                break;
            }

            case IR_NOT: {
                x64_load_vreg(c, REG_RAX, ins->src1);
                x64_test_rr(c, REG_RAX, REG_RAX);
                x64_sete(c);
                x64_movzx_rax_al(c);
                x64_store_vreg(c, ins->dst, REG_RAX);
                break;
            }

            case IR_SHL: {
                x64_load_vreg(c, REG_RAX, ins->src1);
                x64_load_vreg(c, REG_RCX, ins->src2);
                x64_shl_cl(c, REG_RAX);
                x64_store_vreg(c, ins->dst, REG_RAX);
                break;
            }

            case IR_SHR: {
                x64_load_vreg(c, REG_RAX, ins->src1);
                x64_load_vreg(c, REG_RCX, ins->src2);
                x64_shr_cl(c, REG_RAX);
                x64_store_vreg(c, ins->dst, REG_RAX);
                break;
            }

            case IR_EQ:
            case IR_NEQ:
            case IR_LT:
            case IR_GT:
            case IR_LTE:
            case IR_GTE: {
                x64_load_vreg(c, REG_RAX, ins->src1);
                x64_load_vreg(c, REG_RCX, ins->src2);
                x64_cmp_rr(c, REG_RAX, REG_RCX);

                switch (ins->op) {
                    case IR_EQ:  x64_sete(c);  break;
                    case IR_NEQ: x64_setne(c); break;
                    case IR_LT:  x64_setl(c);  break;
                    case IR_GT:  x64_setg(c);  break;
                    case IR_LTE: x64_setle(c); break;
                    case IR_GTE: x64_setge(c); break;
                    default: break;
                }

                x64_movzx_rax_al(c);
                x64_store_vreg(c, ins->dst, REG_RAX);
                break;
            }

            case IR_BOOL_AND: {
                x64_load_vreg(c, REG_RAX, ins->src1);
                x64_load_vreg(c, REG_RCX, ins->src2);

                x64_test_rr(c, REG_RAX, REG_RAX);
                x64_emit2(c, 0x0F, 0x95);
                x64_emit(c, 0xC0);

                x64_test_rr(c, REG_RCX, REG_RCX);
                x64_emit2(c, 0x0F, 0x95);
                x64_emit(c, 0xC1);

                x64_and_rr(c, REG_RAX, REG_RCX);
                x64_movzx_rax_al(c);

                x64_store_vreg(c, ins->dst, REG_RAX);
                break;
            }

            case IR_BOOL_OR: {
                x64_load_vreg(c, REG_RAX, ins->src1);
                x64_load_vreg(c, REG_RCX, ins->src2);

                x64_or_rr(c, REG_RAX, REG_RCX);
                x64_test_rr(c, REG_RAX, REG_RAX);
                x64_setne(c);
                x64_movzx_rax_al(c);

                x64_store_vreg(c, ins->dst, REG_RAX);
                break;
            }

            case IR_JMP: {
                u32 loff = x64_find_label(c, ins->label);

                x64_emit(c, 0xE9);

                if (loff != 0xFFFFFFFF) {
                    x64_emit32(c, loff - c->pos - 4);
                } else {
                    if (patch_count < 1024) {
                        patches[patch_count].name = ins->label;
                        patches[patch_count].site = c->pos;
                        patch_count++;
                    }

                    x64_emit32(c, 0);
                }

                break;
            }

            case IR_JZ:
            case IR_JNZ: {
                u32 loff = x64_find_label(c, ins->label);

                x64_load_vreg(c, REG_RAX, ins->src1);
                x64_test_rr(c, REG_RAX, REG_RAX);

                x64_emit(c, 0x0F);
                x64_emit(c, ins->op == IR_JZ ? 0x84 : 0x85);

                if (loff != 0xFFFFFFFF) {
                    x64_emit32(c, loff - c->pos - 4);
                } else {
                    if (patch_count < 1024) {
                        patches[patch_count].name = ins->label;
                        patches[patch_count].site = c->pos;
                        patch_count++;
                    }

                    x64_emit32(c, 0);
                }

                break;
            }

            case IR_CALL: {
                int ai;

                for (ai = 0; ai < ins->arg_count && ai < 6; ai++) {
                    x64_load_vreg(c, CALL_ARG_REGS[ai], ins->args[ai]);
                }

                for (ai = ins->arg_count - 1; ai >= 6; ai--) {
                    x64_load_vreg(c, REG_RAX, ins->args[ai]);
                    x64_push(c, REG_RAX);
                }

                x64_emit(c, 0x48);
                x64_emit(c, 0x83);
                x64_emit(c, 0xEC);
                x64_emit(c, 8);

                x64_emit(c, 0xE8);

                {
                    u32 loff = x64_find_label(c, ins->fn_name ? ins->fn_name : "");

                    if (loff != 0xFFFFFFFF && ins->fn_name) {
                        x64_emit32(c, loff - c->pos - 4);
                    } else {
                        if (patch_count < 1024 && ins->fn_name) {
                            patches[patch_count].name = ins->fn_name;
                            patches[patch_count].site = c->pos;
                            patch_count++;
                        }

                        x64_emit32(c, 0);
                    }
                }

                x64_emit(c, 0x48);
                x64_emit(c, 0x83);
                x64_emit(c, 0xC4);
                x64_emit(c, 8);

                if (ins->arg_count > 6) {
                    u32 extra = (u32)(ins->arg_count - 6) * 8;
                    x64_add_rsp(c, extra);
                }

                if (ins->dst.kind == IRVAL_REG) {
                    x64_store_vreg(c, ins->dst, REG_RAX);
                }

                break;
            }

            case IR_SYSCALL: {
                int ai;

                for (ai = 0; ai < 7; ai++) {
                    if (ai < ins->arg_count) {
                        x64_load_vreg(c, SYSCALL_ARG_REGS[ai], ins->args[ai]);
                    } else {
                        x64_xor_rr(c, SYSCALL_ARG_REGS[ai], SYSCALL_ARG_REGS[ai]);
                    }
                }

                x64_syscall(c);

                if (ins->dst.kind == IRVAL_REG) {
                    x64_store_vreg(c, ins->dst, REG_RAX);
                }

                break;
            }

            case IR_RET: {
                if (ins->src1.kind != IRVAL_NONE) {
                    x64_load_vreg(c, REG_RAX, ins->src1);
                } else {
                    x64_xor_rr(c, REG_RAX, REG_RAX);
                }

                x64_emit(c, 0x48);
                x64_emit(c, 0x89);
                x64_emit(c, 0xEC);

                x64_pop(c, REG_RBP);
                x64_ret(c);

                break;
            }

            case IR_MALLOC: {
                x64_load_vreg(c, REG_RSI, ins->src1);

                x64_mov_ri64(c, REG_RAX, 9);
                x64_mov_ri64(c, REG_RDI, 0);
                x64_mov_ri64(c, REG_RDX, 3);
                x64_mov_ri64(c, REG_RCX, 0x22);
                x64_mov_ri64(c, REG_R8, (u64)-1LL);
                x64_mov_ri64(c, REG_R9, 0);

                x64_syscall(c);

                if (ins->dst.kind == IRVAL_REG) {
                    x64_store_vreg(c, ins->dst, REG_RAX);
                }

                break;
            }

            case IR_FREE: {
                x64_load_vreg(c, REG_RDI, ins->src1);

                x64_mov_ri64(c, REG_RSI, 4096);
                x64_mov_ri64(c, REG_RAX, 11);

                x64_syscall(c);

                break;
            }

            case IR_CAST: {
                x64_load_vreg(c, REG_RAX, ins->src1);

                if (ins->cast_type && type_is_float(ins->cast_type)) {
                    i32 slot = x64_vreg_slot(c, ins->dst.reg);

                    x64_emit(c, 0xF2);
                    x64_emit(c, 0x48);
                    x64_emit(c, 0x0F);
                    x64_emit(c, 0x2A);
                    x64_emit(c, MODRM(3, 0, REG_RAX));

                    if (slot >= -128 && slot <= 127) {
                        x64_emit(c, 0xF2);
                        x64_emit(c, 0x0F);
                        x64_emit(c, 0x11);
                        x64_emit(c, MODRM(1, 0, REG_RBP));
                        x64_emit(c, (u8)(i8)slot);
                    } else {
                        x64_emit(c, 0xF2);
                        x64_emit(c, 0x0F);
                        x64_emit(c, 0x11);
                        x64_emit(c, MODRM(2, 0, REG_RBP));
                        x64_emit32(c, (u32)slot);
                    }

                    break;
                }

                x64_store_vreg(c, ins->dst, REG_RAX);
                break;
            }

            case IR_FIELD_PTR: {
                x64_load_vreg(c, REG_RAX, ins->src1);

                if (ins->field_idx != 0) {
                    if (ins->field_idx < 128) {
                        x64_emit(c, 0x48);
                        x64_emit(c, 0x83);
                        x64_emit(c, 0xC0);
                        x64_emit(c, (u8)ins->field_idx);
                    } else {
                        x64_emit(c, 0x48);
                        x64_emit(c, 0x05);
                        x64_emit32(c, ins->field_idx);
                    }
                }

                x64_store_vreg(c, ins->dst, REG_RAX);
                break;
            }

            case IR_INDEX_PTR: {
                x64_load_vreg(c, REG_RAX, ins->src1);
                x64_load_vreg(c, REG_RCX, ins->src2);

                x64_add_rr(c, REG_RAX, REG_RCX);

                x64_store_vreg(c, ins->dst, REG_RAX);
                break;
            }

            case IR_PRINT_INT: {
                u32 loff;

                x64_load_vreg(c, REG_RDI, ins->src1);

                x64_emit(c, 0xE8);

                loff = x64_find_label(c, "_forge_print_int");

                if (loff != 0xFFFFFFFF) {
                    x64_emit32(c, loff - c->pos - 4);
                } else {
                    if (patch_count < 1024) {
                        patches[patch_count].name = "_forge_print_int";
                        patches[patch_count].site = c->pos;
                        patch_count++;
                    }

                    x64_emit32(c, 0);
                }

                break;
            }

            case IR_PRINT_STR: {
                if (ins->src1.kind == IRVAL_STR) {
                    u32 stridx = x64_add_string(c, ins->src1.sval ? ins->src1.sval : "");
                    char lbl[32];

                    x64_emit(c, 0x48);
                    x64_emit(c, 0x8D);
                    x64_emit(c, 0x3D);

                    sprintf(lbl, "__str_%u", stridx);
                    x64_add_reloc(c, c->pos, lbl);
                    x64_emit32(c, 0);

                    x64_mov_ri64(c, REG_RSI, (u64)strlen(ins->src1.sval ? ins->src1.sval : ""));
                } else {
                    u32 strlen_loop;
                    u32 je_patch;
                    u32 here;
                    i32 back;

                    x64_load_vreg(c, REG_RDI, ins->src1);

                    x64_push(c, REG_RDI);
                    x64_xor_rr(c, REG_RSI, REG_RSI);

                    strlen_loop = c->pos;

                    x64_emit(c, 0x42);
                    x64_emit(c, 0x80);
                    x64_emit(c, MODRM(0, 7, 4));
                    x64_emit(c, 0x27);
                    x64_emit(c, 0);

                    x64_emit(c, 0x74);

                    je_patch = c->pos;
                    x64_emit(c, 0);

                    x64_emit(c, 0x48);
                    x64_emit(c, 0xFF);
                    x64_emit(c, 0xC6);

                    back = (i32)(strlen_loop - c->pos - 2);
                    x64_emit(c, 0xEB);
                    x64_emit(c, (u8)(i8)back);

                    here = c->pos;
                    c->buf[je_patch] = (u8)(here - je_patch - 1);

                    x64_pop(c, REG_RDI);
                }

                x64_push(c, REG_RDI);
                x64_push(c, REG_RSI);

                x64_mov_ri64(c, REG_RAX, 1);
                x64_mov_ri64(c, REG_RDI, 1);

                x64_pop(c, REG_RDX);
                x64_pop(c, REG_RSI);

                x64_syscall(c);

                x64_emit(c, 0x6A);
                x64_emit(c, 0x0A);

                x64_mov_ri64(c, REG_RAX, 1);
                x64_mov_ri64(c, REG_RDI, 1);

                x64_emit(c, 0x48);
                x64_emit(c, 0x8D);
                x64_emit(c, 0x34);
                x64_emit(c, 0x24);

                x64_mov_ri64(c, REG_RDX, 1);

                x64_syscall(c);

                x64_add_rsp(c, 8);

                break;
            }

            case IR_PRINT_FLOAT: {
                u32 stridx = x64_add_string(c, "FLOAT\n");
                char lbl[32];

                x64_emit(c, 0x48);
                x64_emit(c, 0x8D);
                x64_emit(c, 0x3D);

                sprintf(lbl, "__str_%u", stridx);
                x64_add_reloc(c, c->pos, lbl);
                x64_emit32(c, 0);

                x64_mov_ri64(c, REG_RSI, 6);

                x64_push(c, REG_RDI);
                x64_push(c, REG_RSI);

                x64_mov_ri64(c, REG_RAX, 1);
                x64_mov_ri64(c, REG_RDI, 1);

                x64_pop(c, REG_RDX);
                x64_pop(c, REG_RSI);

                x64_syscall(c);

                break;
            }

            default:
                break;
        }
    }

    {
        u32 p;

        for (p = 0; p < patch_count; p++) {
            u32 loff = x64_find_label(c, patches[p].name);

            if (loff != 0xFFFFFFFF) {
                u32 site = patches[p].site;
                u32 rel = loff - site - 4;

                x64_patch32(c, site, rel);
            }
        }
    }

    free(patches);
}

static void write_le16(u8 *p, u16 v) {
    p[0] = (u8)v;
    p[1] = (u8)(v >> 8);
}

static void write_le32(u8 *p, u32 v) {
    p[0] = (u8)v;
    p[1] = (u8)(v >> 8);
    p[2] = (u8)(v >> 16);
    p[3] = (u8)(v >> 24);
}

static void write_le64(u8 *p, u64 v) {
    p[0] = (u8)v;
    p[1] = (u8)(v >> 8);
    p[2] = (u8)(v >> 16);
    p[3] = (u8)(v >> 24);
    p[4] = (u8)(v >> 32);
    p[5] = (u8)(v >> 40);
    p[6] = (u8)(v >> 48);
    p[7] = (u8)(v >> 56);
}

static void emit_target_binary(const char *out_path, X64Ctx *c, TargetFGL *t) {
    u32 code_size = c->pos;
    u32 str_total = 0;
    u32 code_offset;
    u32 file_size;
    u8 *file;
    u32 i;

    for (i = 0; i < c->str_count; i++) {
        c->strings[i].offset = code_size + str_total;
        str_total += (u32)strlen(c->strings[i].str) + 1;
    }

    for (i = 0; i < c->reloc_count; i++) {
        if (strncmp(c->relocs[i].label, "__str_", 6) == 0) {
            u32 idx = (u32)atoi(c->relocs[i].label + 6);

            if (idx < c->str_count) {
                i32 rel = (i32)(c->strings[idx].offset - c->relocs[i].offset - 4);
                x64_patch32(c, c->relocs[i].offset, (u32)rel);
            }
        }
    }

    if (t->has_code_offset && t->code_offset >= t->header_len) {
        code_offset = t->code_offset;
    } else {
        code_offset = t->header_len;
    }

    file_size = code_offset + code_size + str_total;
    file = (u8*)calloc(file_size ? file_size : 1, 1);

    if (t->header_len) {
        memcpy(file, t->header, t->header_len);
    }

    memcpy(file + code_offset, c->buf, code_size);

    {
        u32 off = 0;

        for (i = 0; i < c->str_count; i++) {
            u32 sl = (u32)strlen(c->strings[i].str) + 1;

            memcpy(file + code_offset + code_size + off, c->strings[i].str, sl);
            off += sl;
        }
    }

    if (t->has_entry_patch) {
        u32 entry_label = x64_find_label(c, "main");
        u64 entry_value;

        if (entry_label == 0xFFFFFFFF) entry_label = 0;

        entry_value = t->entry_base + code_offset + entry_label;

        if (t->entry_patch_offset + t->entry_patch_width > file_size) {
            fprintf(stderr, "forger: entry patch offset is outside output file\n");
            exit(1);
        }

        if (t->entry_patch_width == 4) {
            write_le32(file + t->entry_patch_offset, (u32)entry_value);
        } else {
            write_le64(file + t->entry_patch_offset, entry_value);
        }
    }

    {
        FILE *f = fopen(out_path, "wb");

        if (!f) {
            fprintf(stderr, "forger: cannot open output '%s'\n", out_path);
            exit(1);
        }

        fwrite(file, 1, file_size, f);
        fclose(f);
    }

#if !PLATFORM_WINDOWS
    {
        char cmd[1024];
        snprintf(cmd, sizeof(cmd), "chmod +x \"%s\"", out_path);
        system(cmd);
    }
#endif

    printf(
        "forger: wrote %s -> %s (%u bytes, arch=%s, bits=%u, mode=%s)\n",
        t->ext,
        out_path,
        file_size,
        t->arch,
        t->bits,
        t->mode
    );

    free(file);
}

static char *read_file(const char *path) {
    FILE *f = fopen(path, "rb");
    char *buf;
    long sz;

    if (!f) {
        fprintf(stderr, "forger: cannot open '%s'\n", path);
        exit(1);
    }

    fseek(f, 0, SEEK_END);
    sz = ftell(f);
    fseek(f, 0, SEEK_SET);

    buf = (char*)malloc(sz + 1);

    fread(buf, 1, sz, f);
    fclose(f);

    buf[sz] = '\0';

    return buf;
}

static void usage(void) {
    printf(
        "Forger - FGL-driven compiler\n"
        "\n"
        "Usage: forger <source.fg> -T <target.fgl> [options]\n"
        "\n"
        "Options:\n"
        "  -o <file>        Output file. Default: out.<EXT from target FGL>\n"
        "  -T <file.fgl>    Required FGL target description\n"
        "  -v               Verbose\n"
        "  -h               Show this help\n"
        "\n"
        "FGL target directives:\n"
        "  EXT elf\n"
        "  ARCH x86_64\n"
        "  BITS 64\n"
        "  MODE long\n"
        "  MAGIC 7F 45 4C 46\n"
        "  HEADER-BYTES 02 01 01 00\n"
        "  HEADER-FILE header.bin\n"
        "  CODE-OFFSET 120\n"
        "  ENTRY-PATCH-OFFSET 24\n"
        "  ENTRY-PATCH-WIDTH 8\n"
        "  ENTRY-BASE 0x400000\n"
        "\n"
        "Syscall:\n"
        "  V i64 r = SC(1, 1, msg, len);\n"
        "\n"
        "ASM is disabled. Use SC(...).\n"
    );
}

int main(int argc, char **argv) {
    const char *src_path = NULL;
    const char *out_path = NULL;
    const char *target_path = NULL;
    static char default_out[512];

    int i;

    if (argc < 2) {
        usage();
        return 0;
    }

    for (i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-h") == 0) {
            usage();
            return 0;
        } else if (strcmp(argv[i], "-v") == 0) {
            g_verbose = 1;
        } else if (strcmp(argv[i], "-o") == 0 && i + 1 < argc) {
            out_path = argv[++i];
        } else if (strcmp(argv[i], "-T") == 0 && i + 1 < argc) {
            target_path = argv[++i];
        } else if (argv[i][0] != '-') {
            src_path = argv[i];
        } else {
            fprintf(stderr, "forger: unknown option '%s'\n", argv[i]);
            return 1;
        }
    }

    if (!src_path) {
        fprintf(stderr, "forger: no input file\n");
        return 1;
    }

    if (!target_path) {
        fprintf(stderr, "forger: no FGL target file. Use -T <target.fgl>\n");
        return 1;
    }

    g_source_file = src_path;

    {
        TargetFGL target;

        memset(&target, 0, sizeof(target));
        target.entry_patch_width = 8;

        load_target_fgl(target_path, &target);

        if (!out_path) {
            snprintf(default_out, sizeof(default_out), "out.%s", target.ext[0] ? target.ext : "bin");
            out_path = default_out;
        }

        {
            char *src = read_file(src_path);

            types_init();

            {
                Arena lex_arena;
                Lexer lexer;

                arena_init(&lex_arena);

                memset(&lexer, 0, sizeof(Lexer));

                lexer.src = src;
                lexer.len = (u32)strlen(src);
                lexer.line = 1;
                lexer.col = 1;
                lexer.arena = &lex_arena;

                lexer_lex(&lexer);

                if (g_verbose) {
                    printf("forger: lexed %u tokens\n", lexer.token_count);
                }

                arena_init(&g_ast_arena);

                {
                    Parser parser;
                    ASTNode *program;

                    parser.tokens = lexer.tokens;
                    parser.count = lexer.token_count;
                    parser.pos = 0;
                    parser.arena = &g_ast_arena;

                    program = parse_program(&parser);

                    if (g_error_count) {
                        fprintf(stderr, "forger: %d parse error(s)\n", g_error_count);
                        return 1;
                    }

                    if (g_verbose) {
                        printf("forger: parsed %d top-level statements\n", program->block.count);
                    }

                    {
                        Arena sem_arena;
                        SymTable syms;
                        Semantic sem;
                        int si;

                        arena_init(&sem_arena);

                        symtable_init(&syms, &sem_arena);
                        symtable_push(&syms);

                        sem.syms = &syms;
                        sem.arena = &sem_arena;
                        sem.current_fn_ret = NULL;
                        sem.in_loop = FALSE;

                        for (si = 0; si < program->block.count; si++) {
                            sem_stmt(&sem, program->block.stmts[si]);
                        }

                        if (g_error_count) {
                            fprintf(stderr, "forger: %d semantic error(s)\n", g_error_count);
                            return 1;
                        }

                        if (g_verbose) {
                            printf("forger: semantic analysis passed\n");
                        }

                        {
                            Arena ir_arena;
                            IRBuilder irb;
                            IRLower lower;

                            arena_init(&ir_arena);

                            ir_init(&irb, &ir_arena);

                            lower.b = &irb;
                            lower.arena = &ir_arena;
                            lower.scope = irscope_new(&ir_arena, NULL);

                            lower.break_stack = NULL;
                            lower.cont_stack = NULL;
                            lower.loop_depth = 0;
                            lower.loop_cap = 0;

                            for (si = 0; si < program->block.count; si++) {
                                lower_stmt(&lower, program->block.stmts[si]);
                            }

                            if (g_verbose) {
                                printf("forger: lowered %u IR instructions\n", irb.count);
                            }

                            {
                                Arena cg_arena;
                                X64Ctx ctx;

                                arena_init(&cg_arena);

                                x64_init(&ctx, &cg_arena);
                                x64_emit_runtime_helpers(&ctx);
                                x64_codegen(&ctx, &irb);

                                emit_target_binary(out_path, &ctx, &target);

                                free(ctx.buf);
                                free(ctx.vreg_slots);
                                free(ctx.relocs);
                                free(ctx.labels);
                                free(ctx.strings);
                                free(ctx.frame_patches);

                                arena_free(&cg_arena);
                            }

                            free(lower.break_stack);
                            free(lower.cont_stack);

                            arena_free(&ir_arena);
                        }

                        arena_free(&sem_arena);
                    }
                }

                free(lexer.tokens);
                arena_free(&lex_arena);
            }

            free(src);
            arena_free(&g_ast_arena);
            arena_free(&g_type_arena);

            free(target.header);
        }
    }

    return g_error_count ? 1 : 0;
}
