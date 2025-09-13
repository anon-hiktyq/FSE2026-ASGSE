#include <stdlib.h>
struct list {
  struct list *tail;
};


/*@
  inductive lseg{L}(struct list* x, struct list* y) {
    case nil{L}:
      \forall struct list* x, struct list* y;
        x == y ==> lseg{L}(x, y);

    case cons{L}:
      \forall struct list* x, *y;
        x != y && \valid(x) && \separated(x, y) && lseg{L}(x->tail, y) ==> lseg{L}(x, y);
  }
*/

/*@
  predicate listrep(struct list* head) = lseg(head, NULL);
*/

/*@
  lemma lseg_extend:
    \forall struct list *x, *y;
      lseg(x, y) && \valid(y) && listrep(y) ==> lseg(x, y->tail);
*/

/*@axiomatic List_len {

  logic integer list_len(struct list* start);
  axiom base: \forall struct list* start;
    start == NULL ==> list_len(start) == 0;

  axiom step: \forall struct list* start;
    start != NULL ==> list_len(start) == list_len(start->tail) + 1;
  }
*/

/*@
  requires listrep(head);
  ensures \result == list_len(head); 
*/
int list_length(struct list* head) {
    int count = 0;
    struct list* p = head;

    /*@
      loop invariant listrep(head);
      loop invariant listrep(p);
      loop invariant lseg(head, p);
      loop invariant count == list_len(head) - list_len(p);
      loop assigns p, count;
      loop variant list_len(p); 
    */
    while (p != NULL) {
        count++;
        p = p->tail;
    }

    return count;
}