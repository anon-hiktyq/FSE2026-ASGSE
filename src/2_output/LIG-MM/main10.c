
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        struct sys_slist_t {
    struct sys_slist_t *next;
};

struct sys_slist_t * main10(struct sys_slist_t * x, struct sys_slist_t * y)

/*@

Require emp
Ensure Results(__return)
*/{
    struct sys_slist_t *t, *u;
    if (x == 0) {
        
        
        return y;
    } else {
        t = x;
        u = t->next;
       
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 while (u) {
            t = u;
            u = t->next;
        }
        
        t->next = y;
        return x;
    }
}