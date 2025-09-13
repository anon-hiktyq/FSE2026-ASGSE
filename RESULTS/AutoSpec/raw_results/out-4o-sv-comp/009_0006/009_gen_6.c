
/*@
requires i >= 0 && j >= 0;
*/
void foo009(int i, int j) {

    int x = i;
    int y = j;
    

    /*@
    loop invariant x >= 0;
    loop invariant y >= 0;
    loop invariant i - x == j - y;
    loop invariant y == j - i + x;
    loop invariant x + y == i + j - 2*x;
    loop invariant i - j + y >= 0;
    loop invariant i - j + x <= i;
    loop invariant y == x + (j - i);
    loop invariant y == j - (i - x);
    loop invariant y <= j;
    loop invariant y <= j - (i - x);
    loop invariant y - x == j - i;
    loop invariant y - (j - i) <= x;
    loop invariant x == y + (i - j);
    loop invariant x == i - (j - y);
    loop invariant x <= i;
    loop invariant x + y <= i + j;
    loop invariant j - i <= y;
    loop invariant i - x == j - y;
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
