#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>

#define STACK_SIZE 1024
#define ARENA_BASE_SIZE 4096

typedef enum {
    OP_STORE_LOCAL,
    OP_LOAD_LOCAL,
    OP_LOAD_CONST,
    OP_READ_FIELD,
    OP_BUILD_TYPE,
    OP_RETURN,
    OP_CALL,
    OP_BRANCH_INDEX,
    OP_BRANCH_IF_TRUE,
    OP_JUMP,
    OP_ADD,
    OP_SUB,
    OP_MUL,
    OP_DIV,
    OP_MOD,
    OP_AND,
    OP_OR,
    OP_NOT,
    OP_BIT_AND,
    OP_BIT_OR,
    OP_SHIFT_LEFT,
    OP_SHIFT_RIGHT,
    OP_LESS_NUM,
    OP_LESS_EQUAL_NUM,
    OP_GREATER_NUM,
    OP_GREATER_EQUAL_NUM,
    OP_EQUAL_NUM,
    OP_LESS_STR,
    OP_LESS_EQUAL_STR,
    OP_GREATER_STR,
    OP_GREATER_EQUAL_STR,
    OP_EQUAL_STR,
    OP_NUM,
    OP_BOOL,
    OP_INDEX,

    OP_PUSH,
    OP_HALT,
} Op;

typedef struct {
    uint8_t op;
    uint8_t arg;
} Instruction;

typedef enum {
    TYPE_STR,
    TYPE_BOOL,
    TYPE_NUM,
    TYPE_IDX,
    TYPE_CODE,
    TYPE_OBJ,
} Type;

typedef struct {
    Type type;
    bool marked;
    char bytes[];
} Value;

typedef struct {
    size_t length;
    char value[];
} Str;

typedef struct {
    bool value;
} Bool;

typedef struct {
    size_t value;
} Idx;

typedef struct {
    double value;
} Num;

typedef struct {
    size_t length;
    Instruction code[];
} Code;

typedef struct {
    size_t n_fields;
    Value* fields[];
} Object;

typedef struct frame {
    Value** locals;
    Code* code;
    Instruction *ip;
    struct frame* parent;
} Frame;

typedef struct {
    size_t n_globals;
    Value** globals;
    Value** consts;
} Runtime;

#define STR(val_ptr)  ((Str*)(val_ptr)->bytes)
#define BOOL(val_ptr) ((Bool*)(val_ptr)->bytes)
#define NUM(val_ptr)  ((Num*)(val_ptr)->bytes)
#define IDX(val_ptr)  ((Idx*)(val_ptr)->bytes)
#define CODE(val_ptr) ((Code*)(val_ptr)->bytes)
#define OBJ(val_ptr)  ((Object*)(val_ptr)->bytes)

typedef struct region {
    void* data;
    void* ptr;
    size_t length;
    struct region* prev;
} Region;

typedef struct arena {
    Region* region;
} Arena;

Arena arena1 = { .region = NULL };
Arena arena2 = { .region = NULL };
Arena* arena = &arena1;
Arena* inactive_arena = &arena2;

void alloc_init() {
    arena1.region = malloc(sizeof(Region));
    arena1.region->prev = NULL;
    arena1.region->length = ARENA_BASE_SIZE;
    arena1.region->data = malloc(arena1.region->length);
    arena1.region->ptr = arena1.region->data;

    arena2.region = malloc(sizeof(Region));
    arena2.region->prev = NULL;
    arena2.region->length = ARENA_BASE_SIZE;
    arena2.region->data = malloc(arena2.region->length);
    arena2.region->ptr = arena2.region->data;
}

void* alloc(size_t size) {
    while (1) {
        // Aligned to 16 bytes
        uintptr_t aligned = ((uintptr_t)(arena->region->ptr - 1) & ~0xf) + 16;
        if (aligned + size > (uintptr_t)(arena->region->data + arena->region->length)) {
            Region* prev = arena->region;
            arena->region = malloc(sizeof(Region));
            arena->region->prev = prev;
            arena->region->length = prev->length << 1;
            arena->region->data = malloc(arena->region->length);
            arena->region->ptr = arena->region->data;
        } else {
            arena->region->ptr = (void*)(aligned + size);
            return (void*)aligned;
        }
    }
}

void mark_value(Value* value) {
    if (value->marked) return;
    value->marked = true;
    switch (value->type) {
        case TYPE_STR:
        case TYPE_BOOL:
        case TYPE_NUM:
        case TYPE_IDX:
        case TYPE_CODE:
            break;
        case TYPE_OBJ:
            for (int i = 0; i < OBJ(value)->n_fields; i++)
                mark_value(OBJ(value)->fields[i]);
            break;
    }
}

void mark_stack(Value** stack_base, Value** sp) {
    while (--sp >= stack_base) {
        if (!*sp) continue;
        mark_value(*sp);
    }
}

void gc(Value** stack_base, Value** sp) {
    mark_stack(stack_base, sp);

    // Swap arenas
    Arena* tmp = inactive_arena;
    inactive_arena = arena;
    arena = tmp;

    while (--sp >= stack_base) {
        if (!*sp) continue;
        mark_value(*sp);
    }
}

Value* alloc_bool(bool v) {
    Value* val = malloc(sizeof(Value) + sizeof(Bool));
    val->type = TYPE_BOOL;
    BOOL(val)->value = v;
    return val;
}

Value* alloc_num(double v) {
    Value* val = malloc(sizeof(Value) + sizeof(Num));
    val->type = TYPE_NUM;
    NUM(val)->value = v;
    return val;
}

Value* alloc_idx(size_t v) {
    Value* val = malloc(sizeof(Value) + sizeof(Idx));
    val->type = TYPE_IDX;
    IDX(val)->value = v;
    return val;
}

Value* alloc_code(size_t length) {
    Value* val = malloc(sizeof(Value) + sizeof(Code) + length * sizeof(Instruction));
    val->type = TYPE_CODE;
    CODE(val)->length = length;
    return val;
}

Value* alloc_obj(size_t n_fields) {
    Value* val = malloc(sizeof(Value) + sizeof(Object) + n_fields * sizeof(Value*));
    val->type = TYPE_OBJ;
    OBJ(val)->n_fields = n_fields;
    return val;
}

Frame* alloc_frame(Value** base, Frame* parent, Code* code) {
    Frame* frame = malloc(sizeof(Frame));
    frame->parent = parent;
    frame->locals = base;
    frame->code = code;
    frame->ip = code->code;
    return frame;
}

Frame* free_frame(Frame* frame) {
    Frame* parent = frame->parent;
    free(frame);
    return parent;
}

int str_cmp(Str* lhs, Str* rhs) {
    int smallest = -1;
    int n = lhs->length;
    if (rhs->length < n) {
        smallest = 1;
        n = rhs->length;
    }
    int ret = strncmp(lhs->value, rhs->value, n);
    if (ret == 0 && lhs->length != rhs->length) {
        return smallest;
    }
    return ret;
}

int run(Runtime rt, Code* main) {
    #define POP() (*--sp)
    #define PUSH(v) (*(sp++) = v)
    #define PUSH_SP() (sp++)

    Value** stack = malloc(STACK_SIZE * sizeof(Value*));
    memset(stack, 0, STACK_SIZE * sizeof(Value*));
    Value** sp = stack;
    Frame* frame = malloc(sizeof(Frame));
    frame->locals = rt.globals;
    frame->parent = NULL;
    frame->code = main;
    frame->ip = main->code;
    Value** consts = rt.consts;
    Value *tmp, *lhs, *rhs;

    while (1) {
        switch (frame->ip->op) {
            case OP_STORE_LOCAL:
                frame->locals[frame->ip->arg] = POP();
                break;
            case OP_LOAD_LOCAL:
                PUSH(frame->locals[frame->ip->arg]);
                break;
            case OP_LOAD_CONST:
                PUSH(consts[frame->ip->arg]);
                break;
            case OP_READ_FIELD:
                tmp = POP();
                PUSH(OBJ(tmp)->fields[frame->ip->arg]);
                break;
            case OP_BUILD_TYPE:
                tmp = alloc_obj(frame->ip->arg);
                for (int i = 0; i < frame->ip->arg; i++)
                    OBJ(tmp)->fields[i] = POP();
                PUSH(tmp);
                break;
            case OP_RETURN:
                frame->locals[0] = sp[-1];
                sp = frame->locals + 1;
                frame = free_frame(frame);
                break;
            case OP_CALL:
                tmp = POP();
                frame = alloc_frame(sp-1, frame, CODE(tmp));
                break;
            case OP_BRANCH_INDEX:
                break;
            case OP_BRANCH_IF_TRUE:
                break;
            case OP_JUMP:
                break;
            case OP_ADD:
                lhs = POP();
                rhs = POP();
                PUSH(alloc_num(NUM(lhs)->value + NUM(rhs)->value));
                break;
            case OP_SUB:
                lhs = POP();
                rhs = POP();
                PUSH(alloc_num(NUM(lhs)->value - NUM(rhs)->value));
                break;
            case OP_MUL:
                lhs = POP();
                rhs = POP();
                PUSH(alloc_num(NUM(lhs)->value * NUM(rhs)->value));
                break;
            case OP_DIV:
                lhs = POP();
                rhs = POP();
                PUSH(alloc_num(NUM(lhs)->value / NUM(rhs)->value));
                break;
            case OP_MOD:
                // TODO
                assert(false);
                break;
            case OP_AND:
                lhs = POP();
                rhs = POP();
                PUSH(alloc_bool(BOOL(lhs)->value && BOOL(rhs)->value));
                break;
            case OP_OR:
                lhs = POP();
                rhs = POP();
                PUSH(alloc_bool(BOOL(lhs)->value || BOOL(rhs)->value));
                break;
            case OP_NOT:
                lhs = POP();
                PUSH(alloc_bool(!BOOL(lhs)->value));
                break;
            case OP_BIT_AND:
            case OP_BIT_OR:
            case OP_SHIFT_LEFT:
            case OP_SHIFT_RIGHT:
                // TODO
                assert(false);
                break;
            case OP_LESS_NUM:
                lhs = POP();
                rhs = POP();
                PUSH(alloc_bool(NUM(lhs)->value < NUM(rhs)->value));
                break;
            case OP_LESS_EQUAL_NUM:
                lhs = POP();
                rhs = POP();
                PUSH(alloc_bool(NUM(lhs)->value <= NUM(rhs)->value));
                break;
            case OP_GREATER_NUM:
                lhs = POP();
                rhs = POP();
                PUSH(alloc_bool(NUM(lhs)->value > NUM(rhs)->value));
                break;
            case OP_GREATER_EQUAL_NUM:
                lhs = POP();
                rhs = POP();
                PUSH(alloc_bool(NUM(lhs)->value >= NUM(rhs)->value));
                break;
            case OP_EQUAL_NUM:
                lhs = POP();
                rhs = POP();
                PUSH(alloc_bool(NUM(lhs)->value == NUM(rhs)->value));
                break;
            case OP_LESS_STR:
                lhs = POP();
                rhs = POP();
                PUSH(alloc_bool(str_cmp(STR(lhs), STR(rhs)) < 0));
                break;
            case OP_LESS_EQUAL_STR:
                lhs = POP();
                rhs = POP();
                PUSH(alloc_bool(str_cmp(STR(lhs), STR(rhs)) <= 0));
                break;
            case OP_GREATER_STR:
                lhs = POP();
                rhs = POP();
                PUSH(alloc_bool(str_cmp(STR(lhs), STR(rhs)) > 0));
                break;
            case OP_GREATER_EQUAL_STR:
                lhs = POP();
                rhs = POP();
                PUSH(alloc_bool(str_cmp(STR(lhs), STR(rhs)) >= 0));
                break;
            case OP_EQUAL_STR:
                lhs = POP();
                rhs = POP();
                PUSH(alloc_bool(str_cmp(STR(lhs), STR(rhs)) == 0));
                break;
            case OP_NUM:
                PUSH(alloc_num(frame->ip->arg));
                break;
            case OP_BOOL:
                PUSH(alloc_bool(frame->ip->arg));
                break;
            case OP_INDEX:
                PUSH(alloc_idx(frame->ip->arg));
                break;
            case OP_PUSH:
                for (int i = 0; i < frame->ip->arg; i++)
                    PUSH(NULL);
                break;
            case OP_HALT:
                goto halt;
                break;
        }
        frame->ip++;
    }
halt:
    while (--sp >= stack) {
        if (!*sp) {
            printf("NULL\n");
            continue;
        }
        switch ((*sp)->type) {
            case TYPE_STR:
                printf("%.*s\n", (int)STR(*sp)->length, STR(*sp)->value);
                break;
            case TYPE_BOOL:
                if (BOOL(*sp)->value)
                    printf("true\n");
                else
                    printf("false\n");
                break;
            case TYPE_NUM:
                printf("%lf\n", NUM(*sp)->value);
                break;
            case TYPE_IDX:
                printf("%ld\n", IDX(*sp)->value);
                break;
            case TYPE_CODE:
                printf("..code..\n");
                break;
            case TYPE_OBJ:
                printf("..object..\n");
                break;
        }
    }
    free(stack);
    free(rt.globals);
    free(rt.consts);
    return 0;

    #undef POP
    #undef PUSH
}

const Instruction main_code[] = {
    { .op = OP_LOAD_CONST , .arg = 0 },
    { .op = OP_STORE_LOCAL, .arg = 0 },
    { .op = OP_NUM        , .arg = 2 },
    { .op = OP_LOAD_LOCAL , .arg = 0 },
    { .op = OP_CALL       , .arg = 0 },
    { .op = OP_HALT       , .arg = 0 },
};

const Instruction function[] = {
    { .op = OP_PUSH       , .arg = 1 },
    { .op = OP_LOAD_LOCAL , .arg = 0 },
    { .op = OP_NUM        , .arg = 1 },
    { .op = OP_ADD        , .arg = 0 },
    { .op = OP_RETURN     , .arg = 0 },
};

int main() {
    Runtime rt;
    rt.globals = malloc(1 * sizeof(Value*));

    rt.consts = malloc(1 * sizeof(Value*));

    rt.consts[0] = alloc_code(5);
    memcpy(CODE(rt.consts[0])->code, function, sizeof(function));

    Code* main = malloc(sizeof(Code) + sizeof(main_code));
    main->length = sizeof(main_code) / sizeof(Instruction);
    memcpy(main->code, main_code, sizeof(main_code));

    run(rt, main);
    return 0;
}
