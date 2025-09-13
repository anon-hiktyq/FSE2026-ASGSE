
int main(){

    int x = 0;
    int y = 0;

    /*@
    loop invariant y == x * i; // where i is the number of iterations;
    loop invariant y == x * (y / x + 1);
    loop invariant y == x * (1 + \floor{y/x});
    loop invariant x >= 0 ==> y >= 0;
    loop invariant x == 0;
    loop invariant x == 0 ==> y == 0;
    loop invariant \forall integer k; k >= 0 ==> y >= k;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop assigns y;;
    loop assigns y;
    loop assigns x;
    */
    while(y >= 0){
        y = y + x;
    }


}
