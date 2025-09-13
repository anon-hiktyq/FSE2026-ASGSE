
#include <stdlib.h>

struct sys_slist_t {
    struct sys_slist_t *next;
};

/*@
  predicate listrep(struct sys_slist_t* head) = 
    head == NULL || (\valid(head) && listrep(head->next));
*/

/*@
  requires listrep(l);
  ensures listrep(\result) && l == \at(l, Pre);
*/

struct sys_slist_t *main11(struct sys_slist_t *l)
{
    struct sys_slist_t *p;
    p = l;

    /*@ loop invariant listrep(l);
        loop invariant listrep(p);
        loop invariant \forall struct sys_slist_t *x; 
            (x == l || x == p) ==> listrep(x);
        loop invariant l == \at(l, Pre);
    */
    while (p) {
        p = p->next;
        if (p) {
            p = p->next;
        }
    }

    /*@ assert l == \at(l,Pre); */
    return l;
}
