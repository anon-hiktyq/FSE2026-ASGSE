
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        struct sys_slist_t {
    struct sys_slist_t *next;
};

struct sys_slist_t *main13(struct sys_slist_t *x , struct sys_slist_t *y)

/*@

Require emp
Ensure Results(__return)
*/{
    struct sys_slist_t *z, *t;
    if (x == 0) {
      return y; 
    }
    else {
      z = x;
      t = y;
    
      while (y) {
        t = y -> next;
        y -> next = x -> next;
        x -> next = y;
        if (y -> next == 0) {
          y -> next = t;
          return z;
        }
        else {
          x = y -> next;
          y = t;
        }
      }
      
      
    }
    
    return z;
}