
/*@
requires i >= 0 && j >= 0;
*/
void foo009(int i, int j) {

    int x = i;
    int y = j;
    

    /*@
    loop invariant y == j - x;
    loop invariant y - x == j - i;
    loop invariant x == i - (j - y);;
    loop invariant x == 0 || y != 0;
    loop invariant x <= y + (i - j);
    loop invariant x <= y + (i - j) || x + y <= i + j;
    loop invariant x <= y + (i - j) || j <= y + i - x;
    loop invariant x <= y + (i - j) || i - j <= y;
    loop invariant x <= y + (i - j) || i - (j - y) <= x;
    loop invariant x <= y + (i - j) || 0 <= y;
    loop invariant x < y + (i - j);
    loop invariant x + y == i + j;
    loop invariant x + y <= i + j;
    loop invariant x + y <= i + j || j <= y + i - x;
    loop invariant x + y <= i + j || i - j <= y;
    loop invariant x + y <= i + j || 0 <= y;
    loop invariant x + y < i + j;
    loop invariant x + i == i * 2;
    loop invariant j == y + (i - x);
    loop invariant j <= y + i - x;
    loop invariant j < y + i - x;
    loop invariant j - i + x <= y;
    loop invariant j - i + x <= y || x <= y + (i - j);
    loop invariant j - i + x <= y || x + y <= i + j;
    loop invariant j - i + x <= y || j <= y + i - x;
    loop invariant j - i + x <= y || i - j <= y;
    loop invariant j - i + x <= y || i - (j - y) <= x;
    loop invariant j - i + x <= y || 0 <= y;
    loop invariant j - i + x < y;
    loop invariant i - x == j - y;
    loop invariant i - x <= i;;
    loop invariant i - x <= i || x <= y + (i - j);
    loop invariant i - x <= i || x + y <= i + j;
    loop invariant i - x <= i || j <= y + i - x;
    loop invariant i - x <= i || j - i + x <= y;
    loop invariant i - x <= i || i - j <= y;
    loop invariant i - x <= i || i - (j - y) <= x;
    loop invariant i - x <= i || 0 <= y;
    loop invariant i - x < i;;
    loop invariant i - j <= y;
    loop invariant i - j <= y || j <= y + i - x;
    loop invariant i - j < y;
    loop invariant i - (j - y) <= x;
    loop invariant i - (j - y) <= x || x + y <= i + j;
    loop invariant i - (j - y) <= x || j <= y + i - x;
    loop invariant i - (j - y) <= x || i - j <= y;
    loop invariant i - (j - y) <= x || 0 <= y;
    loop invariant i - (j - y) < x;
    loop invariant \forall integer k; 0 <= k <= j ==> y >= 0;
    loop invariant \forall integer k; 0 <= k <= i ==> x >= 0;
    loop invariant \forall integer k; 0 <= k < i ==> x >= y;
    loop invariant 0 <= y;
    loop invariant 0 <= y || j <= y + i - x;
    loop invariant 0 <= y || i - j <= y;
    loop invariant 0 < y;
    loop invariant y == j - (i - x);
    loop invariant y <= j;
    loop invariant x == i - (j - y);
    loop invariant x == 0 ==> y == j - i;
    loop invariant x <= i;
    loop invariant x - y == i - j;
    loop invariant j <= y + (i - x);
    loop invariant j - i <= y;
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
