
/*@
  requires y > 0; // Ensure y is positive to avoid division by zero
  assigns \result, r, d; // Specify that the result and variables r, d may be modified
  ensures \result * y + r == \at(x, Pre); // Ensure the final relationship holds
  ensures r < y; // Ensure that r is less than y when the loop ends
*/
int goo2(int x, int y) {
    int r = x;
    int d = 0;

    /*@
      loop invariant (\at(x,Pre) >= \at(y,Pre)) ==> (r + d * y == \at(x,Pre));
      loop invariant (\at(x,Pre) >= \at(y,Pre)) ==> (d >= 0);
      loop invariant (!(\at(x,Pre) >= \at(y,Pre))) ==> ((d == 0)&&(r == \at(x,Pre))&&(y == \at(y,Pre))&&(x == \at(x,Pre)));
      loop invariant y == \at(y,Pre);
      loop invariant x == \at(x,Pre);
      loop assigns r, d;
    */
    while (r >= y) {
        // Beginning
        r = r - y;
        d = d + 1;
        // End
        //@ assert r + d*y == x;
    }

    return d;
}
