
#include <stdlib.h>

struct sys_slist_t {
    struct sys_slist_t *next;
};

/*@
  inductive slist_segment{L}(struct sys_slist_t* x, struct sys_slist_t* y) {
    case nil{L}:
      \forall struct sys_slist_t* x, struct sys_slist_t* y;
        x == y ==> slist_segment{L}(x, y);

    case cons{L}:
      \forall struct sys_slist_t* x, struct sys_slist_t* y;
        x != y && \valid(x) && \separated(x, y) && slist_segment{L}(x->next, y) ==> slist_segment{L}(x, y);
  }
*/

/*@
  logic integer list_length(struct sys_slist_t* head) =
    (head == \null ? 0 : 1 + list_length(head->next));
*/

/*@
  predicate slist_valid(struct sys_slist_t* head) = slist_segment(head, \null);
*/

/*@
  requires slist_valid(l);
  ensures slist_valid(\result);
*/
struct sys_slist_t *goo22(struct sys_slist_t *l)
{
    struct sys_slist_t *p;
    p = l;

    /*@ 
        loop invariant slist_valid(l);
        loop invariant slist_valid(p);
        loop assigns p;
        loop variant list_length(p);
    */
    while (p) {
        p = p->next;
    }

    /*@ assert l == \at(l,Pre); */  
    return l;
}
