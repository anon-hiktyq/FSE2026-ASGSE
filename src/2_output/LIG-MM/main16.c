
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        struct SNnode {
    int head;
    struct SNnode *tail;
};


void free_SNnode(struct SNnode *l)/*@

Require emp
Ensure emp
*/
{
}
void * main16(struct SNnode * l)

/*@

Require emp
Ensure Results(__return)
*/{
    struct SNnode *p;
    p = l;
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (listrep(l)) &&
(listrep(p)) &&
(lseg(l, p))
    */
    
    while (l) {
        p = l_tail;
        free_SNnode(l);
        l = p;
    } 
    
}