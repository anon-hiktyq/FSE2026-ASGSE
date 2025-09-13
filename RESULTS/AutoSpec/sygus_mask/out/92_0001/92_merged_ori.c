int main(){

    int x = 0;
    int y = 0;

    /*@
    loop invariant y == x * (y / x);
    loop invariant y == x * (number of iterations);
    loop invariant y == x * (i + 1);
    loop invariant x == 0 ==> y == 0;
    loop invariant \forall integer k; 0 <= k < y ==> y == k + x * (y / x);
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop assigns y;;
    loop assigns y;
    loop assigns x;;
    loop assigns x;
    */
    while(y >= 0){
        y = y + x;
    }


}
