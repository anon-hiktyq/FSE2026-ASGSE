
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        struct list_t {
    struct list_t *next;
};

struct list_t *goo21(struct list_t *l)

/*@

Require emp
Ensure Results(__return)
*/{
    struct list_t *p;
    p = l;
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (listrep(l)) &&
(listrep(p)) &&
(l == l@pre
      loop assigns p
      loop variant length(p))
    */
    
    while (p) {
        p = p->next;
    }
    
    return l;
}