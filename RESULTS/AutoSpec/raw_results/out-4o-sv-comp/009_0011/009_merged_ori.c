
/*@
requires i >= 0 && j >= 0;
*/
void foo009(int i, int j) {

    int x = i;
    int y = j;
    

    /*@
    loop invariant y == j - x;
    loop invariant y + x == j;
    loop invariant x == i - y;
    loop invariant x == i + (j - y);
    loop invariant x <= j;
    loop invariant x <= i && y <= j;
    loop invariant x - y == i - j;
    loop invariant x + y == i + j;
    loop invariant j - y <= j;
    loop invariant i - x == j - y;
    loop invariant i - j <= x - y;
    loop invariant 0 <= y;
    loop invariant y == j - (i - x);
    loop invariant y <= j;
    loop invariant x == i - (j - y);
    loop invariant x <= i;
    loop invariant j - i <= y;
    loop invariant i - x <= i;
    loop invariant 0 <= x;
    loop invariant 0 <= i - x;
    loop assigns y;
    loop assigns x;
    */
    while (x != 0) {
        x--;
        y--;
    }

    if (i == j) {
        // @ assert y == 0;*/
    }
    

}
