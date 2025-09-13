
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
struct SLL * main2(struct SLL *l, int data) 
{
    struct SLL *p;
    p = l;

    /*@ 
      loop invariant listrep(l);
      loop invariant listrep(p);
        (x == l ==> (x->head == data)) || 
        (x != NULL ==> (x->head == data));
    */
    while (p) {
        if (p->head != data) {
            /*@ assert p->head != data; */
            /*@ assert l == \at(l,Pre); */
            return l;
        }
        p = p->tail;
    }

    return l;
}
