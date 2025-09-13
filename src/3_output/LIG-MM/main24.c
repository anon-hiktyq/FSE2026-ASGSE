
#include <stdlib.h>

struct SLL {
    struct SLL *tail;
    int head;
};

/*@ 
  predicate sllrep(struct SLL* head) = 
    head == \null || (\valid(head) && sllrep(head->tail));
*/

/*@ 
  inductive lseg{L}(struct SLL* x, struct SLL* y) {
    case nil{L}:
      \forall struct SLL* x, *y;
        x == y ==> lseg{L}(x, y);

    case cons{L}:
      \forall struct SLL* x, *y;
        x != y && \valid(x) && \separated(x, y) && lseg{L}(x->tail, y) ==> lseg{L}(x, y);
  }
*/

/*@ 
  requires \valid(l);
  ensures l == \null;
*/
void free_SLL(struct SLL *l){
}

/*@ 
  requires sllrep(l);
  ensures l == \null;
*/
void main24(struct SLL *l) 
{
    struct SLL *p;
    p = l;

    /* >>> LOOP INVARIANT TO FILL <<< */

    /*@
      loop invariant sllrep(l);
      loop invariant sllrep(p);
      loop invariant lseg(l, p);
      loop invariant (l == \null) ==> (p == \null);
    */
    while (l) {
        p = l->tail;
        free_SLL(l);
        l = p;
    }

    /*@ assert l == p; */
}
