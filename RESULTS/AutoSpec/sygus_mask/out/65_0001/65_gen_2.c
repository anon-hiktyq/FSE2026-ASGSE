
int main() {
    int x = 1;
    int y = 0;

    /*@
    loop invariant 1 <= x <= 100;
    loop invariant y == 100 - x;
    loop assigns x;
    loop assigns y;
    */
    while (x <= 100) {
        y = 100 - x;
        x = x +1;
    }


}
