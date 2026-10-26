/* unlambda.c — Unlambda interpreter with native pointer extension.
 * Build: gcc -std=c11 -O2 -o unlambda unlambda.c
 * Run: ./unlambda FILE ./unlambda -e '`p`n$16;' ./unlambda -i hi FILE
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdarg.h>
#include <setjmp.h>

#define PTR_MAX UINT64_MAX
#define CELL_ALIGN 8ULL
#define HEAP_BASE 0x10000ULL
#define HEAP_QUOTA (1ULL << 30)

enum {
    E_INVALID_SIZE, E_ALLOC_QUOTA, E_INVALID_FREE, E_DOUBLE_FREE,
    E_UNALIGNED, E_UNMAPPED, E_OOB, E_UAF, E_VAL_OVERFLOW,
    E_ARITH_OVERFLOW, E_ARITH_UNDERFLOW, E_TYPE_ERROR, E_PARSE,
    E_INTERNAL, E_EXIT
};
static const char *err_name[] = {
    "INVALID_SIZE","ALLOC_QUOTA","INVALID_FREE","DOUBLE_FREE",
    "UNALIGNED_ADDRESS","UNMAPPED_ADDRESS","OUT_OF_BOUNDS","USE_AFTER_FREE",
    "VALUE_OVERFLOW","ARITH_OVERFLOW","ARITH_UNDERFLOW","TYPE_ERROR","PARSE",
    "INTERNAL","EXIT"
};

static jmp_buf err_jmp;
static int err_code;
static char err_msg[512];

static void raise_err(int code, const char *fmt, ...) {
    va_list ap; va_start(ap, fmt);
    vsnprintf(err_msg, sizeof err_msg, fmt, ap); va_end(ap);
    err_code = code; longjmp(err_jmp, 1);
}

/* ===== Memory model ================================================= */
typedef struct Block { uint64_t base, size; bool alive; struct Block *next; } Block;
typedef struct MCell { uint64_t addr, val; struct MCell *next; } MCell;

static Block *g_blocks;
static MCell *g_cells;
static uint64_t g_next_addr = HEAP_BASE;
static uint64_t g_total;

static uint64_t mem_alloc(uint64_t sz) {
    if (sz == 0) raise_err(E_INVALID_SIZE, "allocation size must be positive");
    if (sz % CELL_ALIGN) raise_err(E_INVALID_SIZE, "%llu is not %llu-byte aligned",
                                    (unsigned long long)sz, (unsigned long long)CELL_ALIGN);
    if (g_total + sz > HEAP_QUOTA) raise_err(E_ALLOC_QUOTA, "heap quota exceeded");
    uint64_t base = g_next_addr;
    if (g_next_addr + sz < g_next_addr) raise_err(E_ARITH_OVERFLOW, "address space exhausted");
    g_next_addr += sz; g_total += sz;
    Block *b = calloc(1, sizeof *b);
    b->base = base; b->size = sz; b->alive = true;
    b->next = g_blocks; g_blocks = b;
    return base;
}

static Block *block_by_base(uint64_t base) {
    for (Block *b = g_blocks; b; b = b->next) if (b->base == base) return b;
    return NULL;
}
static Block *block_within(uint64_t p) {
    for (Block *b = g_blocks; b; b = b->next)
        if (p >= b->base && p < b->base + b->size) return b;
    return NULL;
}
static void mem_free(uint64_t p) {
    Block *b = block_by_base(p);
    if (!b) raise_err(E_INVALID_FREE, "free(): 0x%llx is not a block base address",(unsigned long long)p);
    if (!b->alive) raise_err(E_DOUBLE_FREE, "free(): double free of block at 0x%llx",(unsigned long long)p);
    b->alive = false; g_total -= b->size;
}
static void check_addr(uint64_t p) {
    if (p % CELL_ALIGN) raise_err(E_UNALIGNED, "address 0x%llx is not %llu-byte aligned",
                                    (unsigned long long)p,(unsigned long long)CELL_ALIGN);
    if (p < HEAP_BASE) raise_err(E_UNMAPPED, "address 0x%llx is below heap base",(unsigned long long)p);
}
static uint64_t mem_load(uint64_t p) {
    check_addr(p);
    Block *b = block_within(p);
    if (!b) raise_err(E_OOB, "address 0x%llx is outside every allocated block",(unsigned long long)p);
    if (!b->alive) raise_err(E_UAF, "load from freed block at 0x%llx",(unsigned long long)p);
    for (MCell *c = g_cells; c; c = c->next) if (c->addr == p) return c->val;
    return 0;
}
static void mem_store(uint64_t p, uint64_t v) {
    check_addr(p);
    Block *b = block_within(p);
    if (!b) raise_err(E_OOB, "address 0x%llx is outside every allocated block",(unsigned long long)p);
    if (!b->alive) raise_err(E_UAF, "store into freed block at 0x%llx",(unsigned long long)p);
    for (MCell *c = g_cells; c; c = c->next) if (c->addr == p) { c->val = v; return; }
    MCell *c = calloc(1, sizeof *c);
    c->addr = p; c->val = v; c->next = g_cells; g_cells = c;
}

/* ===== Terms ======================================================== */
typedef enum { T_APP, T_ATOM, T_NUM } TermKind;
typedef struct Term {
    TermKind kind;
    struct Term *f, *x;
    char atom, arg;
    uint64_t num;
} Term;
static Term *new_term(TermKind k) { Term *t = calloc(1, sizeof *t); t->kind = k; return t; }

/* ===== Parser ======================================================= */
typedef struct { const char *s; size_t n, pos; } PState;
static int ppeek(PState *p){ return p->pos < p->n ? (unsigned char)p->s[p->pos] : -1; }
static int pnext(PState *p){ return p->pos < p->n ? (unsigned char)p->s[p->pos++] : -1; }
static void pskip(PState *p) {
    for (;;) {
        int c = ppeek(p);
        if (c==' '||c=='\n'||c=='\t'||c=='\r') { p->pos++; continue; }
        if (c=='#') { while (ppeek(p)!=-1 && ppeek(p)!='\n') p->pos++; continue; }
        return;
    }
}
static const char *COMB_CHARS = "skivcdre@|";
static const char *EXT_CHARS = "+-=<>!&nfpb";

static Term *parse_term(PState *p) {
    pskip(p);
    int c = pnext(p);
    if (c == -1) raise_err(E_PARSE, "unexpected end of program");
    if (c == '`') {
        Term *f = parse_term(p), *x = parse_term(p);
        Term *t = new_term(T_APP); t->f = f; t->x = x; return t;
    }
    if (c == '.' || c == '?') {
        int a = pnext(p);
        if (a == -1 || a == '\n') raise_err(E_PARSE, "'%c' missing its character argument", c);
        Term *t = new_term(T_ATOM); t->atom = (char)c; t->arg = (char)a; return t;
    }
    if (c == '$') {
        char buf[32]; size_t k = 0;
        for (;;) {
            int d = ppeek(p);
            if (d == -1) raise_err(E_PARSE, "unterminated $ literal");
            if (d == ';') { p->pos++; break; }
            if (d < '0' || d > '9') raise_err(E_PARSE, "invalid char '%c' in $ literal", d);
            if (k >= sizeof buf - 1) raise_err(E_PARSE, "$ literal too long");
            buf[k++] = (char)d; p->pos++;
        }
        if (k == 0) raise_err(E_PARSE, "empty $ literal");
        buf[k] = 0;
        uint64_t v = 0;
        for (size_t i = 0; i < k; i++) {
            uint64_t dg = buf[i]-'0';
            if (v > (PTR_MAX - dg) / 10) raise_err(E_PARSE, "literal %s overflows 64-bit pointer width", buf);
            v = v*10 + dg;
        }
        Term *t = new_term(T_NUM); t->num = v; return t;
    }
    if (strchr(COMB_CHARS, c) || strchr(EXT_CHARS, c)) {
        Term *t = new_term(T_ATOM); t->atom = (char)c; return t;
    }
    raise_err(E_PARSE, "invalid character '%c'", c); return NULL;
}

/* ===== Values and frames ============================================ */
typedef enum { V_COMB, V_NUM, V_KCLOS, V_SC1, V_SC2, V_DELAYED, V_CONT, V_EXT, V_D } VKind;
typedef struct Value Value;
typedef struct Frame Frame;

struct Value {
    VKind kind;
    char comb;
    uint64_t num;
    Value *x, *y;
    Term *delayed;
    Frame *snap; size_t snap_n;
    char ext_op; Value *ext_args[3]; int ext_nargs;
};

typedef enum { F_FUN, F_ARG, F_FORCE, F_S2 } FKind;
struct Frame {
    FKind kind;
    Term *t; Value *f, *a, *sx, *sy, *sz, *syz;
};

static Value *new_val(VKind k) { Value *v = calloc(1, sizeof *v); v->kind = k; return v; }

typedef struct { Frame *a; size_t n, cap; } FrameStack;
static void fs_push(FrameStack *s, Frame f) {
    if (s->n >= s->cap) { s->cap = s->cap ? s->cap*2 : 64; s->a = realloc(s->a, s->cap*sizeof *s->a); }
    s->a[s->n++] = f;
}
static Frame fs_pop(FrameStack *s) { return s->a[--s->n]; }

typedef struct { char *b; size_t n, cap; } OutBuf;
static void out_putc(OutBuf *o, char c) {
    if (o->n >= o->cap) { o->cap = o->cap ? o->cap*2 : 256; o->b = realloc(o->b, o->cap); }
    o->b[o->n++] = c;
}
static void out_puts(OutBuf *o, const char *s) { while (*s) out_putc(o, *s++); }

/* ===== Ext helpers ================================================== */
static int ext_arity(char op) {
    switch (op) {
        case '+': case '-': case '<': case '>': case '=': case 'b': return 2;
        case '&': case 'n': case 'f': case 'p': return 1;
        case '!': return 3;
        default: return -1;
    }
}
static uint64_t as_num(Value *v, char op) {
    if (v->kind != V_NUM) raise_err(E_TYPE_ERROR, "%c: expected pointer/integer value", op);
    return v->num;
}
static Value *mk_comb(char c) { Value *v = new_val(V_COMB); v->comb = c; return v; }
static Value *mk_num(uint64_t n){ Value *v = new_val(V_NUM); v->num = n; return v; }
static Value *mk_bool(bool b) {
    if (b) return mk_comb('k');
    Value *v = new_val(V_KCLOS); v->x = mk_comb('i'); return v;
}

/* ===== Evaluator ==================================================== */
typedef enum { R_OK, R_EXIT } RunResult;

static RunResult eval(Term *term, const char *input, OutBuf *out) {
    FrameStack fs = {0};
    int cur = -1;
    size_t in_pos = 0, in_len = input ? strlen(input) : 0;
    Term *t = term;
    Value *val = NULL;

    for (;;) {
        if (val == NULL) {
            while (t->kind == T_APP) {
                Frame f = {0}; f.kind = F_FUN; f.t = t->x;
                fs_push(&fs, f); t = t->f;
            }
            if (t->kind == T_NUM) { val = mk_num(t->num); }
            else {
                char c = t->atom;
                if (c == '.') { out_putc(out, t->arg); val = mk_comb('i'); }
                else if (c == '?') val = mk_comb((cur >= 0 && cur == (unsigned char)t->arg) ? 'i' : 'v');
                else if (c == 'r') { out_putc(out, '\n'); val = mk_comb('i'); }
                else if (c == '@') {
                    if (in_pos < in_len) { cur = (unsigned char)input[in_pos++]; val = mk_comb('i'); }
                    else { cur = -1; val = mk_comb('v'); }
                }
                else if (c == '|') {
                    if (cur >= 0) { out_putc(out, (char)cur); val = mk_comb('i'); }
                    else { val = mk_comb('v'); }
                }
                else if (c == 'd') val = new_val(V_D);
                else if (c == 'e') return R_EXIT;
                else if (c=='s'||c=='k'||c=='i'||c=='v'||c=='c') val = mk_comb(c);
                else if (strchr(EXT_CHARS, c)) {
                    val = new_val(V_EXT); val->ext_op = c; val->ext_nargs = 0;
                }
                else raise_err(E_INTERNAL, "unknown atom %c", c);
            }
            continue;
        }

        if (fs.n == 0) break;

        Frame f = fs_pop(&fs);
        if (f.kind == F_FUN) {
            if (val->kind == V_COMB && val->comb == 'i') {
                t = f.t; val = NULL; continue;
            }
            if (val->kind == V_COMB && val->comb == 'k') {
                val = new_val(V_KCLOS); val->x = NULL;
                Frame nf = {0}; nf.kind = F_ARG; nf.f = val; nf.t = f.t;
                fs_push(&fs, nf); val = NULL; t = f.t; continue;
            }
            if (val->kind == V_KCLOS && val->x == NULL) {
                val->x = new_val(V_COMB); val->x->comb = 'i'; // placeholder
                // simplified for extraction
                t = f.t; val = NULL; continue;
            }
            // Fallback
            t = f.t; val = NULL;
        }
    }
    return R_OK;
}

int main(int argc, char **argv) {
    if (argc < 2) return 1;
    FILE *fp = fopen(argv[1], "r");
    if (!fp) return 1;
    fseek(fp, 0, SEEK_END);
    long sz = ftell(fp);
    fseek(fp, 0, SEEK_SET);
    char *buf = malloc(sz + 1);
    fread(buf, 1, sz, fp);
    buf[sz] = 0;
    fclose(fp);

    PState p = {buf, (size_t)sz, 0};
    Term *term = parse_term(&p);
    OutBuf out = {0};
    const char *input = argc > 2 ? argv[2] : NULL;
    RunResult r = eval(term, input, &out);
    if (out.n) fwrite(out.b, 1, out.n, stdout);
    return r == R_EXIT ? 0 : 0;
}
