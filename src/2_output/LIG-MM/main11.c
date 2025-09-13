
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        struct sys_slist_t {
    struct sys_slist_t *next;
};

struct sys_slist_t *main11(struct sys_slist_t *l)

/*@

Require emp
Ensure Results(__return)
*/{
    struct sys_slist_t *p;
    p = l;
   
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (listrep(l)) &&
(listrep(p)) &&
(\forall struct sys_slist_t *x 
            (x == l || x == p) => listrep(x)) &&
(l == l@pre)
    */
    
    while (p) {
        p = p->next;
        if (p) {
            p = p->next;
        }
    }
    
    return l;
}