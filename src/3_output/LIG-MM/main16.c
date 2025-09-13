
#include <stdlib.h>

struct SNnode {
    int head;
    struct SNnode *tail;
};

/*@
  inductive lseg(struct SNnode* x, struct SNnode* y) {
    case nil:
      \forall struct SNnode* x, struct SNnode* y;
        x == y ==> lseg(x, y);

    case cons:
      \forall struct SNnode* x, *y;
        x != y && \valid(x) && \separated(x, y) && lseg(x->tail, y) ==> lseg(x, y);
  }
*/

/*@
  lemma lseg_extend:
    \forall struct SNnode *x, *y;
      lseg(x, y) && \valid(y) && lseg(y, NULL) ==> lseg(x, y->tail);
*/

/*@
  predicate listrep(struct SNnode* head) = lseg(head, NULL);
*/

/*@
    requires \valid(l);
    ensures l == \null;
    */
void free_SNnode(struct SNnode *l) {
}

/*@
    requires listrep(l);
    ensures l == \null;
    */
void * main16(struct SNnode * l) {
    struct SNnode *p;
    p = l;

    /*@ loop invariant listrep(l);
        loop invariant listrep(p);
        loop invariant lseg(l, p);
    */
    while (l) {
        p = l->tail;
        free_SNnode(l);
        l = p;
    }

    /*@ assert l == p; */
}
