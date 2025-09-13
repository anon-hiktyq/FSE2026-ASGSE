
/*@
requires i >= 0 && j >= 0;
*/
void foo009(int i, int j) {

    int x = i;
    int y = j;
    

    /*@
    loop invariant x - i == y - j;
    loop invariant x + y == x + j - i;
    loop invariant x + y == i + j;
    loop invariant x + y == i + j - 2 * (i - x);
    loop invariant x + i <= j + y;
    loop invariant x + i <= j + y || 0 <= y;
    loop invariant x + i <= j + y || 0 <= x - y;
    loop invariant x + i < j + y;
    loop invariant j - y == i - x;
    loop invariant i - j <= x - y;
    loop invariant i - j <= x - y || x + i <= j + y;
    loop invariant i - j <= x - y || 0 <= y;
    loop invariant i - j <= x - y || 0 <= x - y;
    loop invariant i - j < x - y;
    loop invariant \forall integer k; 0 <= k <= i ==> x <= k + x;
    loop invariant 0 <= y;
    loop invariant 0 <= y || 0 <= x - y;
    loop invariant 0 <= x - y;
    loop invariant 0 < y;
    loop invariant 0 < x - y;
    loop invariant 0 < x - y;
    loop invariant 0 < x - y;
    loop invariant 0 < x - y;
    loop invariant 0 < x - y;
    loop invariant 0 < x - y;
    loop invariant 0 < x - y;
    loop invariant 0 < x - y;
    loop invariant 0 < x - y;
    loop invariant 0 < x - y;
    loop invariant 0 < x - y;
    loop invariant 0 < x - y;
    loop invariant 0 < x - y;
    loop invariant 0 < x - y;
    loop invariant 0 < x - y;
    loop invariant 0 < x - y;
    loop invariant 0 < x - y;
    loop invariant 0 < x - y;
    loop invariant y == j - (i - x);
    loop invariant y <= j;
    loop invariant y - (j - i) <= x;
    loop invariant x == i - (j - y);
    loop invariant x <= i;
    loop invariant x - y == i - j;
    loop invariant x + y <= i + j;
    loop invariant x + (j - i) == y;
    loop invariant j - i <= y;
    loop invariant j - (i - x) <= y;
    loop invariant i - x == j - y;
    loop invariant i - j == x - y;
    loop invariant 0 <= x;
    loop invariant 0 <= j;
    loop invariant 0 <= i;
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
