
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        struct SNnode {
    int head;
    struct SNnode *tail;
};

struct SNnode *main7(struct SNnode *p)

/*@

Require emp
Ensure Results(__return)
*/{
    struct SNnode *w, *t, *v;
    w = 0;
    v = p;
    
    while (v) {
        t = v->tail;
        v->tail = w;
        w = v;
        v = t;
    }
    
    return w;
}