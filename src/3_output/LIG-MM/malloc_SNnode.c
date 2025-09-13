struct SNnode {
    int head;
    struct SNnode *tail;
};
/*@
    ensures \valid(\result);
ensures \result->head == data;
ensures \result->tail == \null;
    */
    
struct SNnode* malloc_SNnode(int data){
}