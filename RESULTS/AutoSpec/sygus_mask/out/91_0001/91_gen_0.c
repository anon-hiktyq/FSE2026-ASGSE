
int main(){

    int x = 0;
    int y = 0;

    /*@
    loop invariant y >= 0;
    loop invariant x >= 0;
    loop invariant \forall integer k; k >= 0 ==> y >= k;
    loop assigns y;
    loop assigns x;
    */
    while(y >= 0){
        y = y + x;
    }


}
