
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        struct SLL {
    struct SLL *tail;
    int head;
};

struct SLL * main1(struct SLL *l, int data) 

/*@

Require emp
Ensure Results(__return)
*/{
    struct SLL *p;
    p = l;

    while (p) {
      if (p->head == data) {
        
        
        return l;
      }
      p = p->tail;
    }
    return l;
}