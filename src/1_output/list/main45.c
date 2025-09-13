
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        struct sys_slist_t {
    struct sys_slist_t *next;
};

struct sys_slist_t *main45(struct sys_slist_t *l)

/*@

Require emp
Ensure Results(__return)
*/{
    struct sys_slist_t *p;
    p = l;
   
    while (p) {
        p = p->next;
    }
    
    return l;
}