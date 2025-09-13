#include <stdlib.h>

struct list {
    struct list *tail;
};


/*@
  inductive lseg{L}(struct list* x, struct list* y) {
    case nil{L}:
      \forall struct list* x, struct list* y;
        x == y ==> lseg{L}(x, y);

    case cons{L}:
      \forall struct list* x, *y;
        x != y && \valid(x) && \separated(x, y) && lseg{L}(x->tail, y) ==> lseg{L}(x, y);
  }
*/

/*@
  lemma lseg_extend:
    \forall struct list *x, *y;
      lseg(x, y) && \valid(y) && listrep(y) ==> lseg(x, y->tail);
*/

/*@
  predicate listrep(struct list* head) = lseg(head, NULL);
*/



/*@
  requires listrep(l);
  ensures listrep(\result);
*/
struct list *iter_twice(struct list *l)
{
    struct list *p;
    p = l;
   

    /*@ loop invariant listrep(l);
        loop invariant listrep(p);
        loop invariant lseg(l, p);
    */
    while (p) {
        p = p->tail;
        if (p) {
          p = p -> tail;
        }
    }
    return l;
}