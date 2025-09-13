
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        struct SNnode {
    int head;
    struct SNnode *tail;
};


struct SNnode* malloc_SNnode(int data)/*@

Require emp
Ensure Results(__return)
*/
{
}
struct SNnode * main18(struct SNnode * x, int data)

/*@

Require emp
Ensure Results(__return)
*/{
    struct SNnode *p;
    p = x;
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 while (p) {
      if (p->tail == 0) {
        p -> tail = malloc_SNnode(data);
        p = p -> tail;
      }
      p = p -> tail;
    }
    
    return x;
}