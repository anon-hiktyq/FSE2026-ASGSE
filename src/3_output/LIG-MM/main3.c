
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
  requires listrep(l);
  ensures listrep(\result);
*/
struct SLL * main3(struct SLL *l, int data) 
{
    struct SLL *p;
    p = l;

    /*@
      loop invariant listrep(l);
      loop invariant listrep(p);
          listrep(x) ==> (x->head == data || x == p);
    */
    while (p) {
        if (p->head != data) {
            p->head = data;
        }
        p = p->tail;
    }

    /*@ assert \forall struct SLL *x; listrep(x) ==> (x->head == data); */
    /*@ assert listrep(l); */
    return l;
}
