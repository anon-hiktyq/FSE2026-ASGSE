struct SLL {
    struct SLL *tail;
    int head;
  };
/*@
    ensures \valid(\result);
  ensures \result->head == data;
  ensures \result->tail == \null;
    */
    
struct SLL* malloc_SLL(int data){
  }