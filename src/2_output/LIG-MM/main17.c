
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
struct SNnode * main17(struct SNnode * x, int data)

/*@

Require emp
Ensure Results(__return)
*/{
    struct SNnode *p, *new_node;
    new_node = 0;
    p = x;
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (listrep(x)) &&
(listrep(p))
    */
    
    while (p) {
        if (p->head < data) {
            new_node = malloc_SNnode(data);
            if (new_node != NULL) {
                new_node->tail = p->tail;
                p->tail = new_node;
                return x;
            }
        }
        p = p->tail;
    }
    
    return x;
}