
struct SLL {
    struct SLL *tail;
    int head;
};

struct SLL * main40(struct SLL *l, int data) 
{
    struct SLL *p;
    p = l;

    /*@
    loop invariant p == \at(p, Pre) || p == 0;
    loop invariant \forall integer k; \valid(p) ==> (\forall integer j; 0 <= j < k ==> \at(p, Pre)->head != data);
    loop assigns p;
    */
    while (p) {
        if (p->head == data) {
            /*@ assert l == \at(l,Pre); */
            /*@ assert data == \at(data,Pre); */
            return l;
        }
        p = p->tail;
    }
    return l;
}
