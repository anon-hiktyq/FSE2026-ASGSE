
int main() {
    int x = 1;
    int y = 0;

    /*@
    loop invariant x >= 1 && x <= 11;
    loop invariant y == 10 - x;
    loop assigns x;
    loop assigns y;
    */
    while (x <= 10) {
        y = 10 - x;
        x = x +1;
    }


}
