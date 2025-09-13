
/*@
requires i >= 0 && j >= 0;
*/
void foo009(int i, int j) {

    int x = i;
    int y = j;
    

    /*@
    loop invariant x >= 0 && y >= 0;
    loop invariant x >= y - (j - i);
    loop invariant i - j == x - y;
    loop invariant x <= i;
    loop invariant y <= j;
    loop assigns x, y;
    */
    while (x != 0) {
        x--;
        y--;
    }

    if (i == j) {
        // @ assert y == 0;*/
    }
    

}
