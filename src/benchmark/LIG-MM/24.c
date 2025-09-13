//SV-COMP remove_all            
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
  
  
  void main24(struct SLL *l) 
  {
    struct SLL *p;
    p = l;
    while (l) {
      p = l->tail;
      free_SLL(l);
      l = p;
    }
    /*@ assert l == p; */
  }