
#include <stdlib.h>

struct list_t {
    struct list_t *next;
};

/*@
  inductive lseg{L}(struct list_t* x, struct list_t* y) {
    case nil{L}:
      \forall struct list_t* x, struct list_t* y;
        x == y ==> lseg{L}(x, y);

    case cons{L}:
      \forall struct list_t* x, *y;
        x != y && \valid(x) && lseg{L}(x->next, y) ==> lseg{L}(x, y);
  }
*/

/*@
  predicate listrep(struct list_t* head) = lseg(head, NULL);
*/

/*@
  logic integer length{L}(struct list_t* x) =
    (x == NULL ? 0 : 1 + length{L}(x->next));
*/

/*@
  requires listrep(l);
  ensures listrep(\result);
*/
struct list_t *goo21(struct list_t *l)
{
    struct list_t *p;
    p = l;
    
    /*@ 
      loop invariant listrep(l);
      loop invariant listrep(p);
      loop invariant l == \at(l,Pre);
      loop assigns p;
      loop variant length(p);
    */
    while (p) {
        p = p->next;
    }
    
    /* MASK_ACSL_ASSERT */
    return l;
}
