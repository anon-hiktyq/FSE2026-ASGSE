struct SNnode {
    int head;
    struct SNnode *tail;
};
/*@
    requires \valid(l);
ensures l == \null;
    */
    
void free_SNnode(struct SNnode *l){
}