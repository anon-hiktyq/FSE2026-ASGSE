
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        struct sys_slist_t {
    struct sys_slist_t *next;
};

struct sys_slist_t *main48(struct sys_slist_t *p)

/*@

Require emp
Ensure Results(__return)
*/{
    struct sys_slist_t *w, *t, *v;
    w = 0;
    v = p;
    while (v) {
        t = v->next;
        v->next = w;
        w = v;
        v = t;
    }
    
    return w;
}