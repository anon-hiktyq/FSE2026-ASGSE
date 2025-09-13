//SV-COMP prepend_unequal
#include <stdlib.h>
struct SLL {
  struct SLL *tail;
  int head;
};


/*@
ensures \valid(\result);
ensures \result->head == data;
ensures \result->tail == \null;
*/
struct SLL* malloc_SLL(int data);

/*@
requires \valid(l);
ensures l == \null;
*/
void free_SLL(struct SLL *l);


struct SLL * main22(struct SLL *l, int data) 
{
  struct SLL *p;
  l = prepend(l, data);
  p = l;
  
  while (p) {
    if (p->head == data) {
      return l;
    }
    p = p->tail;
  }
  /*@ assert data == \at(data,Pre); */
  return l;
}