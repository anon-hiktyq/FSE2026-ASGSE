
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        struct list_t {
    struct list_t *next;
};

struct list_t *main46(struct list_t *l)

/*@

Require emp
Ensure Results(__return)
*/{
    struct list_t *p;
    p = l;
    while (p) {
        p = p->next;
        if (p) {
          p = p -> next;
        }
      	else {
          return l;
        }
    }
    
    return l;
}