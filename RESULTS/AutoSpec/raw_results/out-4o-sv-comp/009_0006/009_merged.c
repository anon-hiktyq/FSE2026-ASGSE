
/*@
requires i >= 0 && j >= 0;
*/
void foo009(int i, int j) {

    int x = i;
    int y = j;
    

    /*@
    loop invariant y == j - x + i - x;
    loop invariant y == j - i + x;
    loop invariant y == j - (j - y);
    loop invariant x == i - y + j - y;
    loop invariant x == i - (i - x);
    loop invariant x - y == i - j;
    loop invariant x + y == i + j;
    loop invariant x + y == i + j - 2*x;
    loop invariant x + y == i + j - (i - x);
    loop invariant j - y == i - x;
    loop invariant j - y <= y;
    loop invariant j - y <= y || i - x <= x;
    loop invariant j - y <= y || i - j + x <= i;
    loop invariant j - y <= y || 0 <= y;
    loop invariant j - y <= y || 0 <= i - j + y;
    loop invariant j - y < y;
    loop invariant i - x <= x;
    loop invariant i - x <= x || i - j + x <= i;
    loop invariant i - x <= x || 0 <= y;
    loop invariant i - x <= x || 0 <= i - j + y;
    loop invariant i - x < x;
    loop invariant i - x + j - y == 0;
    loop invariant i - j == x - y;
    loop invariant i - j + x <= i;
    loop invariant i - j + x <= i || 0 <= i - j + y;
    loop invariant i - j + x < i;
    loop invariant i + j == x + y;
    loop invariant 0 <= y;
    loop invariant 0 <= y || i - j + x <= i;
    loop invariant 0 <= y || 0 <= i - j + y;
    loop invariant 0 <= x && 0 <= y;
    loop invariant 0 <= i - j + y;
    loop invariant 0 < y;
    loop invariant 0 < i - j + y;
    loop invariant 0 < i - j + y;
    loop invariant 0 < i - j + y;
    loop invariant 0 < i - j + y;
    loop invariant 0 < i - j + y;
    loop invariant 0 < i - j + y;
    loop invariant 0 < i - j + y;
    loop invariant 0 < i - j + y;
    loop invariant 0 < i - j + y;
    loop invariant 0 < i - j + y;
    loop invariant 0 < i - j + y;
    loop invariant 0 < i - j + y;
    loop invariant 0 < i - j + y;
    loop invariant 0 < i - j + y;
    loop invariant 0 < i - j + y;
    loop invariant 0 < i - j + y;
    loop invariant 0 < i - j + y;
    loop invariant 0 < i - j + y;
    loop invariant y == x + (j - i);
    loop invariant y == j - (i - x);
    loop invariant y <= j;
    loop invariant y <= j - (i - x);
    loop invariant y - x == j - i;
    loop invariant y - (j - i) <= x;
    loop invariant x == y + (i - j);
    loop invariant x == i - (j - y);
    loop invariant x <= i;
    loop invariant x + y <= i + j;
    loop invariant j - i <= y;
    loop invariant i - x == j - y;
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
