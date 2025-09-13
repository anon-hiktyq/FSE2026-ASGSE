
#include <stdlib.h>

struct sys_slist_t {
    struct sys_slist_t *next;
};

/*@
  predicate lseg{L}(struct sys_slist_t* x, struct sys_slist_t* y) =
    x == y || (x != 0 && \valid(x) && lseg(x->next, y));

  predicate listrep(struct sys_slist_t* head) = lseg(head, 0);
*/

/*@
    requires \at(x,Pre) != 0 && (y == \at(y,Pre)) && (x == \at(x,Pre));
    ensures listrep(\result);
    */
    
struct sys_slist_t *main13(struct sys_slist_t *x , struct sys_slist_t *y)
{
    struct sys_slist_t *z, *t;
    if (x == 0) {
      return y; 
    }
    else {
      z = x;
      t = y;
    
      
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            */
            while (y) {
        t = y -> next;
        y -> next = x -> next;
        x -> next = y;
        if (y -> next == 0) {
          y -> next = t;
          return z;
        }
        else {
          x = y -> next;
          y = t;
        }
      }
            
      /*@ assert y == t ;*/
      /*@ assert x != 0; */
    }
    
    return z;
}
