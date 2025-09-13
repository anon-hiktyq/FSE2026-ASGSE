
#include <stdlib.h>

struct list_t {
    struct list_t *next;
};

/*@
  inductive lseg{L}(struct list_t* x, struct list_t* y) {
    case nil{L}:
      \forall struct list_t* x; 
        lseg(x, NULL);

    case cons{L}:
      \forall struct list_t* x, *y;
        x != y && \valid(x) && \separated(x, y) && lseg(x->next, y) ==> lseg(x, y);
  }
*/

/*@
  predicate listrep(struct list_t* head) = lseg(head, NULL);
*/

/*@
    requires listrep(l);
    ensures listrep(\result);
    ensures \result == l; // Ensure that the return value is the same as the input list
    */
    
struct list_t *main9(struct list_t *l)
{
    struct list_t *p;
    p = l;

    /*@ loop invariant listrep(l);
        loop invariant p == NULL || listrep(p);
        loop invariant lseg(l, p); // Ensure that the segment from l to p is valid
    */
    while (p) {
        p = p->next;
        if (p) {
            p = p->next;
        } else {
            return l;
        }
    }

    /*@ assert l == \at(l,Pre); */
    return l;
}
