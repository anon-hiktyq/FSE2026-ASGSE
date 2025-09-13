
struct list_t {
    struct list_t *next;
};

struct list_t *main46(struct list_t *l)
{
    struct list_t *p;
    p = l;
    /*@
    loop invariant p == \at(p, Pre) || p == 0;
    loop invariant \forall integer i; \valid(l) ==> (p == \at(l, Pre) || p == 0);
    loop assigns p;
    */
    while (p) {
        p = p->next;
        if (p) {
            p = p -> next;
        }
        else {
            return l;
        }
    }
    /*@ assert l == \at(l, Pre); */
    return l;
}
