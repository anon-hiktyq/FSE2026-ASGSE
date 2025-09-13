
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        struct SLL {
    struct SLL *tail;
    int head;
  };

struct SLL* malloc_SLL(int data)
/*@

Require emp
Ensure Results(__return)
*/{
  }