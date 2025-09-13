
#include <stdlib.h>

struct SLL {
    struct SLL *tail;
    int head;
};

/*@
  predicate listrep(struct SLL* head) = \valid(head) && (head == NULL || listrep(head->tail));
*/

/*@
    ensures \valid(\result);
    ensures \result->head == data;
    ensures \result->tail == \null;
*/
struct SLL* malloc_SLL(int data){
}

/*@
    requires listrep(l);
    ensures listrep(\result);
*/
struct SLL * main20(struct SLL *l, int data) {
    struct SLL *p;
    struct SLL *new_node;
    new_node = 0;
    p = l;
    
    /*@ loop invariant listrep(l);
        loop invariant p == \null || (listrep(p) && \valid(p));
    */
    while (p) {
        if (p-> head != data) {
            new_node = malloc_SLL(data);
            new_node->tail = p->tail;
            p->tail = new_node;
            return l;
        }
        p = p->tail;
    }
    
    /*@ assert data == \at(data, Pre); */
    return l;
}
