
#include <stdlib.h>

struct list_t {
    struct list_t *next;
};

/*@ 
  predicate listrep(struct list_t* head) = head == NULL || \valid(head) && listrep(head->next);
*/

/*@ 
  inductive lseg{L}(struct list_t* x, struct list_t* y) {
    case nil{L}:
      \forall struct list_t* x; x == y ==> lseg(x, y);
    case cons{L}:
      \forall struct list_t* x, *y; // Correctly bind y here
        x != y && \valid(x) && \separated(x, y) && lseg(x->next, y) ==> lseg(x, y);
  }
*/

/*@ 
  requires listrep(l);
  ensures listrep(\result);
*/
struct list_t *main8(struct list_t *l)
{
    struct list_t *p;
    p = l;

    /*@ loop invariant listrep(l);
        loop invariant listrep(p);
        loop invariant lseg(l, p);
    */
    while (p) {
        p = p->next;
    }

    /*@ assert l == \at(l,Pre); */
    return l;
}
