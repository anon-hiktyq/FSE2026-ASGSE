
struct sys_slist_t {
    struct sys_slist_t *next;
};

struct sys_slist_t * main42(struct sys_slist_t * x, struct sys_slist_t * y)

{
    struct sys_slist_t *t, *u;
    if (x == 0) {
        /*@ assert x == \at(x,Pre); */
        /*@ assert y == \at(y,Pre); */
        return y;
    } else {
        t = x;
        u = t->next;
        /*@
        loop invariant u == 0 || \exists struct sys_slist_t *p; p == x && \valid(p);
        loop assigns t, u;
        */
        while (u) {
            t = u;
            u = t->next;
        }
        t->next = y;
        return x;
    }
}
