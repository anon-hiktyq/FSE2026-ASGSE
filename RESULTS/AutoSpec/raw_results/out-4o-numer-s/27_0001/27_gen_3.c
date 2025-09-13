/*@
  requires x >= 0;
  requires y >= 1;
*/
void hoo27(int x,int y) {
    int q = 0;
    int a = 0;
    int b = x;

    /*@
    loop invariant b >= 0;
    loop invariant a >= 0;
    loop invariant 0 <= a < y;
    loop invariant q * y + a + b == x;
    loop assigns a, b, q;
    */
    while(b != 0) {
        if (a + 1 == y) {
            q = q + 1;
            a = 0;
            b = b - 1;
        }
        else {
            a = a + 1;
            b = b - 1;
        }
    }

    /*@ assert q * y + a + b == x; */
}