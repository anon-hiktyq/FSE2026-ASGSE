
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
    requires listrep(p);
    ensures listrep(\result);
    */
    
struct sys_slist_t *main14(struct sys_slist_t *p)
{
    struct sys_slist_t *w, *t, *v;
    w = 0;
    v = p;
    
            
    /*@ loop invariant listrep(w) || w == 0; 
    */
    while (v) {
        t = v->next;
        v->next = w;
        w = v;
        v = t;
    }
            
    /*@ assert listrep(w); */
    return w;
}
