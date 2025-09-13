
/*@
requires i >= 0 && j >= 0;
*/
void foo009(int i, int j) {

    int x = i;
    int y = j;
    

    /*@
    loop invariant y == j - (i - x);
    loop invariant y <= j;
    loop invariant y - x == j - i;
    loop invariant x >= 0 && y >= 0;
    loop invariant x == y + (i - j);
    loop invariant x <= i;
    loop invariant x + y == i + j;
    loop invariant i - x <= i;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop invariant 0 <= i - x;
    loop invariant (i >= j) ==> y >= 0;
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
