
#include <stdlib.h>

struct SNnode {
    int head;
    struct SNnode *tail;
};

/*@
  ensures \valid(\result);
  ensures \result->head == data;
  ensures \result->tail == \null;
*/
struct SNnode* malloc_SNnode(int data){
}

/*@
  predicate snode_rep(struct SNnode* head) = \valid(head) && (head->tail == \null || snode_rep(head->tail));
*/

/*@
  requires snode_rep(x);
  ensures snode_rep(\result);
*/
struct SNnode * main18(struct SNnode * x, int data)
{
    struct SNnode *p;
    p = x;

    /*@ loop invariant snode_rep(x); */ // The list starting from x remains valid
    /*@ loop invariant snode_rep(p) || p == \null; */ // Ensures p is valid or null
    /*@ loop invariant \forall struct SNnode *n; snode_rep(n) ==> (n->tail == \null || snode_rep(n->tail)); */ // Ensures all nodes in the list are valid
    while (p) {
        if (p->tail == 0) {
            p->tail = malloc_SNnode(data);
            p = p->tail;
        }
        p = p->tail;
    }

    /*@ assert \valid(x); */ // Assert that the original list is still valid
    /*@ assert data == \at(data, Pre); */ // Ensure that data remains unchanged
    return x;
}
