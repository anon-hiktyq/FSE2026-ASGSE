
#include <stdlib.h>

struct SNnode {
    int head;
    struct SNnode *tail;
};

int main43(struct SNnode * x, int data)
{
    struct SNnode * p;
    p = x;
   
    /*@
    loop invariant \valid(p) || p == 0;
    loop invariant \forall struct SNnode* q; \lseg(x, q) ==> (q->head != data);
    loop assigns p;
    */
    while (p) {
      if (p->head == data) {
        return 1;
      }
      p = p->tail;
    }
    /*@ assert data == \old(data); */
    /*@ assert x == \at(x,Pre); */
    return -1;
}
