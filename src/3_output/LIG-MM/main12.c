
#include <stdlib.h>

struct sys_slist_t {
    struct sys_slist_t *next;
};

/*@
  inductive lseg{L}(struct sys_slist_t* x, struct sys_slist_t* y) {
    case nil{L}:
      \forall struct sys_slist_t* x, struct sys_slist_t* y;
        x == y ==> lseg{L}(x, y);

    case cons{L}:
      \forall struct sys_slist_t* x, *y;
        x != y && \valid(x) && \separated(x, y) && lseg{L}(x->next, y) ==> lseg{L}(x, y);
  }
*/

/*@
  predicate listrep(struct sys_slist_t* head) = lseg(head, NULL);
*/

/*@
  requires listrep(l);
  ensures listrep(\result);
*/
struct sys_slist_t *main12(struct sys_slist_t *l)
{
    struct sys_slist_t *p;
    p = l;

    /*@ loop invariant listrep(l);
        loop invariant listrep(p);
        loop invariant lseg(l, p) || (p == NULL && listrep(l)); 
    */
    while (p) {
        p = p->next;
    }
    
    /*@ assert listrep(l); */
    return l;
}
