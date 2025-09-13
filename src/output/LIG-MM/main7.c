
#include <stdlib.h>

struct SNnode {
    int head;
    struct SNnode *tail;
};

/*@
  predicate lseg{L}(struct SNnode* x, struct SNnode* y) =
    x == y || (x != NULL && \valid(x) && lseg(x->tail, y));

  predicate listrep(struct SNnode* head) = lseg(head, NULL);
*/

/*@
    requires listrep(p);
    ensures listrep(\result);
    */
    
struct SNnode *main7(struct SNnode *p)
{
    struct SNnode *w, *t, *v;
    w = 0;
    v = p;
    
    /*@ loop invariant lseg(w, NULL);
    */
    while (v) {
        t = v->tail;
        v->tail = w;
        w = v;
        v = t;
    }
    
    /*@ assert listrep(p); */
    return w;
}
