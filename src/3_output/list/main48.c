
struct sys_slist_t {
    struct sys_slist_t *next;
};


struct sys_slist_t *main48(struct sys_slist_t *p)
{
    struct sys_slist_t *w, *t, *v;
    w = 0;
    v = p;
    /*@
    loop invariant v == 0 || \exists struct sys_slist_t *x; x == v;
    loop invariant \forall struct sys_slist_t *x; \at(x, Pre) ==> (x->next == \at(x->next, Pre));
    loop invariant \forall struct sys_slist_t *x; x == w ==> x->next == \at(w, Pre);
    loop assigns w, v, t;
    loop variant \exists struct sys_slist_t *x; x == v;
    */
    while (v) {
        t = v->next;
        v->next = w;
        w = v;
        v = t;
    }
    /*@ assert p == \at(p,Pre); */
    return w;
}
