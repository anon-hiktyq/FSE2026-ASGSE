
struct SNnode {
    int head;
    struct SNnode *tail;
};

struct SNnode * main41(struct SNnode * x, struct SNnode * y)

{
    struct SNnode *t, *u;
    if (x == 0) {
        /*@ assert x == \at(x,Pre); */
        /*@ assert y == \at(y,Pre); */
        return y;
    } else {
        t = x;
        u = t->tail;

        /*@
        loop invariant \exists struct SNnode *p; p == x ==> \valid(p) && (\forall struct SNnode *q; q == p ==> \valid(q->tail));
        loop assigns t, u;
        */
        while (u) {
            t = u;
            u = t->tail;
        }
        t->tail = y;
        return x;
    }
}
