
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        struct SLL {
    struct SLL *tail;
    int head;
  };


struct SLL* malloc_SLL(int data)/*@

Require emp
Ensure Results(__return)
*/
{
  }
struct SLL * main20(struct SLL *l, int data) 
/*@

Require emp
Ensure Results(__return)
*/{
    struct SLL *p;
    struct SLL *new_node;
    new_node = 0;
    p = l;
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 while (p) {
      if (p-> head != data) {
        new_node = malloc_SLL(data);
        new_node->tail = p->tail;
        p->tail = new_node;
        return l;
      }
      p = p->tail;
    }
    
    return l;
  }