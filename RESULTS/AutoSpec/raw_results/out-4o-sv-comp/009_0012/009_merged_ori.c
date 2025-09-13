
/*@
requires i >= 0 && j >= 0;
*/
void foo009(int i, int j) {

    int x = i;
    int y = j;
    

    /*@
    loop invariant y == j - i + x;
    loop invariant y <= x;
    loop invariant y < x;
    loop invariant x == i - j + y;
    loop invariant x == i - j + (j - y);
    loop invariant x + y == i + j;
    loop invariant j - x == i - y;
    loop invariant j - i <= x - y;
    loop invariant j - i <= x - y || y <= x;
    loop invariant j - i <= x - y || i - j <= x;
    loop invariant j - i <= x - y || 0 <= y;
    loop invariant j - i < x - y;
    loop invariant i - j == x - y;
    loop invariant i - j <= x;
    loop invariant i - j <= x || y <= x;
    loop invariant i - j < x;
    loop invariant i + j == x + y;
    loop invariant \forall integer k; 0 <= k <= j-y ==> x <= i - k;
    loop invariant \forall integer k; 0 <= k <= i-x ==> y <= j - k;
    loop invariant 0 <= y;
    loop invariant 0 <= y || y <= x;
    loop invariant 0 <= y || i - j <= x;
    loop invariant 0 < y;
    loop invariant y == j - (i - x);
    loop invariant y <= j;
    loop invariant x == i - (j - y);
    loop invariant x <= i;
    loop invariant x <= i && y <= j;
    loop invariant x - y == i - j;
    loop invariant j - i <= y;
    loop invariant i - x == j - y;
    loop invariant i - x <= i;
    loop invariant i - j <= x - y;
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
