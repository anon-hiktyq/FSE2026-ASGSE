
/*@ 
  requires \valid(r);
  requires y > 0;
  assigns *r;
  ensures *r == x % y; // Final value of *r after the loop is the remainder.
  ensures \result == (x - *r) / y; // The result is the count of how many times y was subtracted from x.
*/
int fun28(int x, int y, int *r) {
    *r = x;
    int d = 0;

    /*@
      loop invariant (\at(*r,Pre) >= \at(y,Pre)) ==> (*r + d * y == \at(x,Pre));
      loop invariant (\at(*r,Pre) >= \at(y,Pre)) ==> (d >= 0);
      loop invariant y == \at(y,Pre);
      loop invariant x == \at(x,Pre);
      loop assigns *r, d;
      loop variant *r;
    */
    while (*r >= y) {
        *r = *r - y;
        d = d + 1;
    }
    
    return d;
}
