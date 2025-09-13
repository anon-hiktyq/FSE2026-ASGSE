
#include <stdlib.h>

struct SNnode {
    int head;
    struct SNnode *tail;
};

/*@
    inductive lseg{L}(struct SNnode* x, struct SNnode* y) {
        case lseg_nil{L}:
            \forall struct SNnode* x, struct SNnode* y;
            x == y ==> lseg{L}(x, y);

        case lseg_cons{L}:
            \forall struct SNnode* x, *y;
            x != y && \valid(x) && \separated(x, y) && lseg{L}(x->tail, y) ==> lseg{L}(x, y);
    }
*/

/*@
    predicate listrep(struct SNnode* head) = lseg(head, NULL);
*/

/*@
    ensures \valid(\result);
    ensures \result->head == data;
    ensures \result->tail == \null;
    ensures listrep(\result);
    */
struct SNnode* malloc_SNnode(int data){
    struct SNnode* node = malloc(sizeof(struct SNnode));
    if (node != NULL) {
        node->head = data;
        node->tail = NULL;
    }
    return node;
}

/*@
    requires listrep(x);
    ensures listrep(\result);
    */
struct SNnode * main17(struct SNnode * x, int data)
{
    struct SNnode *p, *new_node;
    new_node = 0;
    p = x;

    /*@
      loop invariant listrep(x);
      loop invariant listrep(p);
    */
    while (p) {
        if (p->head < data) {
            new_node = malloc_SNnode(data);
            if (new_node != NULL) {
                new_node->tail = p->tail;
                p->tail = new_node;
                return x;
            }
        }
        p = p->tail;
    }

    /*@ assert data == \at(data,Pre); */
    return x;
}
