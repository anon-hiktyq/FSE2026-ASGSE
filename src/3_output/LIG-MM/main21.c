
#include <stdlib.h>

struct SLL {
    struct SLL *tail;
    int head;
};

/*@
  predicate listrep(struct SLL* head) = 
    head == \null || (\valid(head) && listrep(head->tail));
*/

/*@
  requires \valid(\result);
  ensures \result != \null;
  ensures \result->tail == \null;
  ensures \result->head == \at(data, Pre); // Specify that head is set by the caller
*/
struct SLL* malloc_SLL(int data){
}

/*@
  requires listrep(l);
  ensures listrep(\result);
*/
struct SLL * main21(struct SLL *l, int data) {
    struct SLL *p;
    struct SLL *new_node;
    new_node = 0;
    p = l;

    /*@ loop invariant listrep(l);
        loop invariant listrep(p);
        loop invariant \valid(p);
        loop invariant \forall struct SLL *x; lseg(l, p) ==> (x->head != data);
    */
    while (p) {
        if (p->head == data) {
            new_node = malloc_SLL(data);
            new_node->tail = p->tail;
            p->tail = new_node;
            return l;
        }
        p = p->tail;
    }

    /*@ assert data == \at(data,Pre); */
    return l;
}
