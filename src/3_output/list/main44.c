
struct list_t {
    struct list_t *next;
};

struct list_t *main44(struct list_t *l)
{
    struct list_t *p;
    p = l;
    /*@
    loop invariant p == \at(p, Pre) || p == 0;
    loop invariant \forall struct list_t *q; lseg(l, q) ==> (q != p);
    loop assigns p;
    */
    while (p) {
        p = p->next;
    }
    /*@ assert l == \at(l, Pre); */
    return l;
}
