
#include <stdlib.h>

struct sys_slist_t {
    struct sys_slist_t *next;
};

/*@
  predicate lseg{L}(struct sys_slist_t* x, struct sys_slist_t* y) =
    x == y || (x != NULL && \valid(x) && lseg(x->next, y));

  predicate listrep(struct sys_slist_t* head) = lseg(head, NULL);
*/

/*@
    requires listrep(p) && (q == \at(q, Pre)) && (p == \at(p, Pre));
    ensures listrep(\result);
*/
struct sys_slist_t *main15(struct sys_slist_t *p, struct sys_slist_t *q)
{
    struct sys_slist_t *w, *t, *v;
    w = q;
    v = p;

    /*@ loop invariant (w == NULL) || listrep(w);
    */
    while (v) {
        t = v->next;
        v->next = w;
        w = v;
        v = t;
    }

    /*@ assert p == \at(p,Pre); */
    /*@ assert q == \at(q,Pre); */
    return w;
}
