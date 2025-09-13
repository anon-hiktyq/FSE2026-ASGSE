
#include <stdlib.h>

struct sys_slist_t {
    struct sys_slist_t *next;
};

/*@
  predicate lseg{L}(struct sys_slist_t* x, struct sys_slist_t* y) =
    x == y || (x != 0 && \valid(x) && lseg(x->next, y));
*/

/*@
    requires x == 0 || \valid(x);
    ensures \valid(\result) && lseg(x, \result);
    */
    
struct sys_slist_t * main10(struct sys_slist_t * x, struct sys_slist_t * y)
{
    struct sys_slist_t *t, *u;
    if (x == 0) {
        /*@ assert x == \at(x,Pre); */
        /*@ assert y == \at(y,Pre); */
        return y;
    } else {
        t = x;
        u = t->next;
        
        /* >>> LOOP INVARIANT TO FILL <<< */
        
        /*@
          loop invariant (t != 0 ==> \valid(t));
        */
            while (u) {
            t = u;
            u = t->next;
        }
            
        /*@ assert u == t->next; */
        t->next = y;
        return x;
    }
}
