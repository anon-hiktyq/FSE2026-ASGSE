
int main() {
    int x = 1;
    int y = 0;

    /*@
    loop invariant 1 <= x <= 101;
    loop invariant 0 <= y <= 100;
    loop assigns x;
    loop assigns y;
    */
    while (x <= 100) {
        y = 100 - x;
        x = x +1;
    }


}
