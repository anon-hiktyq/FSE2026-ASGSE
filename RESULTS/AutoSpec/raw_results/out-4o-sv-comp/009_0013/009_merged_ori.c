
/*@
requires i >= 0 && j >= 0;
*/
void foo009(int i, int j) {

    int x = i;
    int y = j;
    

    /*@
    loop invariant y >= 0 ==> x == 0;
    loop invariant y == j - \at(x,Pre);
    loop invariant y == j - (i - x);
    loop invariant y <= j;
    loop invariant x == i - \at(x,Pre);
    loop invariant x == 0 ==> y == j - i;
    loop invariant x <= i;
    loop invariant x - y == i - j;
    loop invariant j - (i - x) <= y;
    loop invariant i - x == j - y;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
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
