
#include <stdlib.h>

struct sys_slist_t {
    struct sys_slist_t *next;
};

struct sys_slist_t *main45(struct sys_slist_t *l)
{
    struct sys_slist_t *p;
    p = l;
   
    /*@
    loop invariant p == \null || \valid(p);
    loop assigns p;
    */
    while (p) {
        p = p->next;
    }
    /*@ assert l == \at(l,Pre); */
    return l;
}
