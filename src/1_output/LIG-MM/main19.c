
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
struct SNnode * main19(struct SNnode * x)

/*@

Require emp
Ensure Results(__return)
*/{
    struct SNnode *y, *p, *t;
    y = malloc_SNnode(0);
    t = y;
    p = x;

    while (p) {
      t -> head = p -> head;
      t -> tail = malloc_SNnode(0);
      p = p -> tail;
      t = t -> tail;
    }
    
    
    return y;
}