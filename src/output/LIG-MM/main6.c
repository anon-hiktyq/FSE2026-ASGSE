
#include <stdlib.h>

struct SNnode {
    int head;
    struct SNnode *tail;
};

/*@
  predicate lseg(struct SNnode* x, struct SNnode* y) =
    x == y || (x != NULL && \valid(x) && lseg(x->tail, y));
*/

/*@
  predicate listrep(struct SNnode* head) = lseg(head, NULL);
*/

/*@
    requires listrep(x);
    ensures \result == 1 ==> (x != NULL && x->head == data) && listrep(x);
    ensures \result == -1 ==> (x == NULL || (x != NULL && x->head != data)) && listrep(x);
    assigns \result;
*/
int main6(struct SNnode * x, int data)
{
    struct SNnode * p;
    p = x;

    /*@ loop invariant listrep(x);
        loop invariant lseg(x, p);
    */
    while (p) {
        if (p->head == data) {
            /*@ assert data == data; */
            /*@ assert x == x; */
            return 1;
        }
        p = p->tail;
    }

    return -1;
}
