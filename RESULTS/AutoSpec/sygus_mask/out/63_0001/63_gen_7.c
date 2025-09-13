
int main() {
    int x = 1;
    int y = 0;

    /*@
    loop invariant 1 <= x <= 11;
    loop invariant \forall integer k; 1 <= k < x ==> 0 <= 10 - k < 10;
    loop assigns x;
    loop assigns y;
    */
    while (x <= 10) {
        y = 10 - x;
        x = x +1;
    }


}
