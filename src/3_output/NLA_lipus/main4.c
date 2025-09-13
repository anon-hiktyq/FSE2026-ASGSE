
/*@
  predicate div_invariant(int x, int y, int q, int r) = 
      0 <= q && 0 <= r && r < y && x == q * y + r;

*/

/*@ 
    requires x > 0;
    requires y > 0;
*/
int main4(int x, int y) {
    int q = 0;
    int r = 0;

    /* >>> LOOP INVARIANT TO FILL <<< */

    /*@
        loop invariant (\at(x,Pre) > \at(y,Pre) * 0 + 0) ==> (x >= y * q + r);
        loop invariant (\at(x,Pre) > \at(y,Pre) * 0 + 0) ==> (r < y);
        loop invariant (\at(x,Pre) > \at(y,Pre) * 0 + 0) ==> (0 <= q);
        loop invariant (\at(x,Pre) > \at(y,Pre) * 0 + 0) ==> (0 <= r);
        loop invariant (!(\at(x,Pre) > \at(y,Pre) * 0 + 0)) ==> ((r == 0) && (q == 0) && (y == \at(y,Pre)) && (x == \at(x,Pre)));
        loop invariant y == \at(y,Pre);
        loop invariant x == \at(x,Pre);
        loop assigns q, r;
    */
    while (x > y * q + r) {
        if (r == y - 1) {
            r = 0;
            q += 1;
        } else {
            r += 1;
        }
    }

    /*@ assert(x == q * y + r); */
}
