//SLing delete_all
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
struct SNnode* malloc_SNnode(int data);


/*@
requires \valid(l);
ensures l == \null;
*/
void free_SNnode(struct SNnode *l);

void * main16(struct SNnode * l)
{
    struct SNnode *p;
    p = l;
    
    while (l) {
      p = l->tail;
      free_SNnode(l);
      l = p;
    } 
    /*@ assert l == p; */
}