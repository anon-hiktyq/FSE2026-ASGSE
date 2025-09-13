
int main() {
    int x = 1;
    int y = 0;

    /*@
    loop invariant x >= 1 && x <= 101;
    loop invariant y == 100 - x;
    loop assigns y;
    loop assigns x;
    */
    while (x <= 100) {
        y = 100 - x;
        x = x +1;
    }


}
