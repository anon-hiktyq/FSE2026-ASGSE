
#include <stdlib.h>

struct SNnode {
    int head;
    struct SNnode *tail;
};

/*@
  predicate lseg{L}(struct SNnode* x, struct SNnode* y) =
    x == y || (x != 0 && \valid(x) && lseg(x->tail, y));

  predicate listrep(struct SNnode* head) = lseg(head, 0);
*/

/*@
    requires listrep(x) && \valid(y);
    ensures listrep(\result);
    */
    
struct SNnode * main5(struct SNnode * x, struct SNnode * y)

{
    struct SNnode *t, *u;
    if (x == 0) {
        /*@ assert x == \at(x,Pre); */
        /*@ assert y == \at(y,Pre); */
        return y;
    } else {
        t = x;
        u = t->tail;

        
        /* >>> LOOP INVARIANT TO FILL <<< */
        
        /*@
          loop invariant listrep(x);
        */
            while (u) {
            t = u;
            u = t->tail;
        }
            
        t->tail = y;
        return x;
    }
}
