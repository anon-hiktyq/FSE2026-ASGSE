
struct SNnode {
    int head;
    struct SNnode *tail;
};

struct SNnode *main47(struct SNnode *p)
{
    struct SNnode *w, *t, *v;
    w = 0;
    v = p;
    
    /*@
    loop invariant \forall struct SNnode *x; x == \at(v, Pre) ==> (x == 0 || x->tail == w);
    loop invariant \forall struct SNnode *x; x == \at(w, Pre) ==> (x == 0 || x->tail == w);
    loop invariant \forall struct SNnode *x; x == \at(p, Pre) ==> (x == 0 || x->tail == w);
    loop assigns w;
    loop assigns v;
    loop assigns t;
    */
    while (v) {
        t = v->tail;
        v->tail = w;
        w = v;
        v = t;
    }
    /*@ assert p == \at(p,Pre); */
    return w;
}
