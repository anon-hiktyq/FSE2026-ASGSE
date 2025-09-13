
#include <stdlib.h>

struct SLL {
    struct SLL *tail;
    int head;
};

/*@
  predicate listrep(struct SLL* head) = 
    head == NULL || (head->head == head->head && \valid(head->tail) && listrep(head->tail));
*/

/*@
    requires \valid(l);
    ensures \result == l;
    */
struct SLL * prepend(struct SLL *l, int data){
}

/*@
    requires listrep(l);
    ensures listrep(\result);
    */
struct SLL * main23(struct SLL *l, int data) 
{
    struct SLL *p;
    l = prepend(l, data);
    p = l;

    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
    */
    while (p) {
        if (p->head != data) {
            return l;
        }
        p = p->tail;
    }

    /*@ assert data == data; */
    return l;
}
