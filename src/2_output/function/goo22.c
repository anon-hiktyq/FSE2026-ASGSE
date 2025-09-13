
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        struct sys_slist_t {
    struct sys_slist_t *next;
};

struct sys_slist_t *goo22(struct sys_slist_t *l)

/*@

Require emp
Ensure Results(__return)
*/{
    struct sys_slist_t *p;
    p = l;
   
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (slist_valid(l)) &&
(slist_valid(p)
        loop assigns p
        loop variant list_length(p))
    */
    
    while (p) {
        p = p->next;
    }
    
    return l;
}