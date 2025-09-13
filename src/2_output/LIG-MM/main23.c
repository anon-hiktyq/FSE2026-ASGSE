
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        struct SLL {
  struct SLL *tail;
  int head;
};


struct SLL * prepend(struct SLL *l, int data)/*@

Require emp
Ensure Results(__return)
*/
{
}
struct SLL * main23(struct SLL *l, int data) 
  
/*@

Require emp
Ensure Results(__return)
*/{
    struct SLL *p;
    l = prepend(l, data);
    p = l;
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 while (p) {
      if (p->head != data) {
        return l;
      }
      p = p->tail;
    }
    
    return l;
  }