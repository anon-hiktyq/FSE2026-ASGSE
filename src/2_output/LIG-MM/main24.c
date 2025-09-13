
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        struct SLL {
    struct SLL *tail;
    int head;
  };


void free_SLL(struct SLL *l)/*@

Require emp
Ensure emp
*/
{
  }
void main24(struct SLL *l) 
  
/*@

Require emp
Ensure emp
*/{
    struct SLL *p;
    p = l;
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (sllrep(l)) &&
(sllrep(p)) &&
(lseg(l, p)) &&
((l == \null) => (p == \null))
    */
    
    while (l) {
        p = l_tail;
        free_SLL(l);
        l = p;
    }
    
  }