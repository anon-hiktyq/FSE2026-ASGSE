int main(){

    int x = 0;
    int y = 0;

    /*@
    loop invariant y >= 0;
    loop invariant \forall integer k; 0 <= k <= y ==> y >= 0;
    loop assigns y;
    */
    while(y >= 0){
        y = y + x;
    }

    //post-condition
    // @ assert  y >= 0;
}
