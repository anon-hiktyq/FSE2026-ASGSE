
/*@
requires i >= 0 && j >= 0;
*/
void foo009(int i, int j) {

    int x = i;
    int y = j;
    

    /*@
    loop invariant x >= 0;
    loop invariant y == j - (i - x);
    loop invariant x <= i;
    loop assigns x;
    loop assigns y;
    */
    while (x != 0) {
        x--;
        y--;
    }

    if (i == j) {
        // @ assert y == 0;*/
    }
    

}
