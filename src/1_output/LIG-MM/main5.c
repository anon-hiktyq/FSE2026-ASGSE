
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        struct SNnode {
    int head;
    struct SNnode *tail;
};

struct SNnode * main5(struct SNnode * x, struct SNnode * y)


/*@

Require emp
Ensure Results(__return)
*/{
    struct SNnode *t, *u;
    if (x == 0) {
        
        
        return y;
    } else {
        t = x;
        u = t->tail;

        while (u) {
            t = u;
            u = t->tail;
        }
        t->tail = y;
        return x;
    }
}