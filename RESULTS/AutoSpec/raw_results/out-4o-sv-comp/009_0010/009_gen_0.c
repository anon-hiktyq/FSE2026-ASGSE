
/*@
requires i >= 0 && j >= 0;
*/
void foo009(int i, int j) {

    int x = i;
    int y = j;
    

    /*@
    loop invariant x >= 0;
    loop invariant \forall integer k; 0 <= k <= i - x ==> y == j - k;
    loop invariant x == i - (j - y);
    loop invariant x >= 0 && y >= 0 && (i - x) + (j - y) == i + j;
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
