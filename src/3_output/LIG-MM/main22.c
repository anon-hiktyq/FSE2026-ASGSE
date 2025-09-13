
#include <stdlib.h>

struct SLL {
    struct SLL *tail;
    int head;
};

/*@
  inductive lseg{L}(struct SLL* x, struct SLL* y) {
    case nil{L}:
      \forall struct SLL* x, struct SLL* y;
        x == y ==> lseg{L}(x, y);

    case cons{L}:
      \forall struct SLL* x, *y;
        x != y && \valid(x) && \separated(x, y) && lseg{L}(x->tail, y) ==> lseg{L}(x, y);
  }
*/

/*@
  predicate listrep(struct SLL* head) = lseg(head, NULL);
*/

/*@
    requires \valid(l);
    ensures \result == l;
    */
struct SLL *prepend(struct SLL *l, int data) {
}

/*@
    requires listrep(l);
    ensures listrep(\result);
    */
struct SLL *main22(struct SLL *l, int data) 
{
    struct SLL *p;
    l = prepend(l, data);
    p = l;

    /*@ loop invariant listrep(l);
    */
    while (p) {
        if (p->head == data) {
            return l;
        }
        p = p->tail;
    }

    /*@ assert \forall struct SLL *x; lseg(l, x) ==> (x->head != data); */
    return l;
}
