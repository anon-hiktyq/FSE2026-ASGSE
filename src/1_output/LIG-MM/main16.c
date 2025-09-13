
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
    
    while (l) {
      p = l->tail;
      free_SNnode(l);
      l = p;
    } 
    
}