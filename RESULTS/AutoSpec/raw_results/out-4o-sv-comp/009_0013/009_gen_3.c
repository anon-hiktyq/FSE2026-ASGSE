
/*@
requires i >= 0 && j >= 0;
*/
void foo009(int i, int j) {

    int x = i;
    int y = j;
    

    /*@
    loop invariant x >= 0;
    loop invariant y >= 0;
    loop invariant x == i - \at(x,Pre);
    loop invariant y == j - \at(x,Pre);
    loop invariant x <= i;
    loop invariant y <= j;
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
