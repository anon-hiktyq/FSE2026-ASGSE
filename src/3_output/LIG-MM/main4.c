
#include <stdlib.h>

struct SLL {
    struct SLL *tail;
    int head;
};

/*@
  predicate listrep(struct SLL* head) = 
    head == NULL || (\valid(head) && listrep(head->tail));
*/

/*@
    requires \valid(p) && listrep(p) && (data == \at(data,Pre));
    ensures listrep(\result);
*/
struct SLL * main4(struct SLL *p, int data) 
{
    struct SLL *w, *t, *v;
    w = (void *)0;
    v = p;

    /*@ loop invariant listrep(w); // Invariant reflects the reversed part of the list
        loop invariant listrep(v); // Invariant reflects the current node being processed
        loop invariant \forall struct SLL *x; (x == w) ==> (x->head == data); // Ensures all processed nodes have their head set to data
    */
    while (v) {
        t = v->tail;
        v->tail = w;
        if (v-> head != data) {
            v -> head = data;
        }
        w = v;
        v = t;
    }

    /*@ assert \forall struct SLL *y; listrep(y) ==> (y->head == data); */ // Ensures all nodes have their head set to data
    /*@ assert w == \at(v,Pre); */ // This assertion reflects the new head of the reversed list
    return w;
}
