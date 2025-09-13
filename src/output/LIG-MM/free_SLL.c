struct SLL {
    struct SLL *tail;
    int head;
  };
/*@
    requires \valid(l);
  ensures l == \null;
    */
    
void free_SLL(struct SLL *l){
  }