
/*@
requires i >= 0 && j >= 0;
*/
void foo009(int i, int j) {

    int x = i;
    int y = j;
    

    /*@
    loop invariant x + y == i + j;
    loop invariant x >= 0;
    loop invariant y >= 0;
    loop invariant \abs(x - y) == \abs(i - j);
    loop invariant x + (j - y) == i;
    loop invariant i - x == j - y;  
    loop invariant \max(x, y) <= \max(i, j);
    loop invariant y == j - (i - x);
    loop invariant y <= j;
    loop invariant x == y + (i - j);
    loop invariant x == i - (j - y);
    loop invariant x == 0 ==> y == j - i;
    loop invariant x <= i;
    loop invariant x - y == i - j;
    loop invariant x - i == y - j;
    loop invariant j - i + x == y;
    loop invariant j - (i - x) <= y;
    loop invariant i - x == j - y;
    loop invariant 0 <= x;
    loop invariant 0 <= j - y;
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
