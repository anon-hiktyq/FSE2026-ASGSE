struct SLL {
  struct SLL *tail;
  int head;
};
/*@
    requires \valid(l);
ensures \result == l;
    */
    
struct SLL * prepend(struct SLL *l, int data){
}