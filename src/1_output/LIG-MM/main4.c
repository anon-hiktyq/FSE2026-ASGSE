
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        struct SLL {
    struct SLL *tail;
    int head;
  };

struct SLL * main4(struct SLL *p, int data) 
  
/*@

Require emp
Ensure Results(__return)
*/{
    struct SLL *w, *t, *v;
    w = (void *)0;
    v = p;
    while (v) {
      t = v->tail;
      v->tail = w;
      if (v-> head != data) {
        v -> head = data;
      }
      w = v;
      v = t;
    }
    
    
    return w;
  }