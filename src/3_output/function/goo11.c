
/*@
axiomatic Division {
  logic integer quotient(integer x, integer y);
  logic integer remainder(integer x, integer y);

  axiom division_definition:
    \forall integer x, integer y; y > 0 ==> x == quotient(x, y) * y + remainder(x, y);

  axiom remainder_bounds:
    \forall integer x, integer y; y > 0 ==> 0 <= remainder(x, y) < y;
}
*/

/*@
requires y > 0;
ensures \result == quotient(x, y);
*/
int goo11(int x, int y) {
    int r = x;
    int d = 0;

    /*@
      loop invariant (\at(x,Pre) >= \at(y,Pre)) ==> (r == \at(x,Pre) - d * \at(y,Pre));
      loop invariant (\at(x,Pre) >= \at(y,Pre)) ==> (d == quotient(\at(x,Pre) - r, \at(y,Pre)));
      loop invariant (!(\at(x,Pre) >= \at(y,Pre))) ==> ((d == 0)&&(r == \at(x,Pre))&&(y == \at(y,Pre))&&(x == \at(x,Pre)));
      loop invariant y == \at(y,Pre);
      loop invariant x == \at(x,Pre);
      loop assigns r, d;
      loop variant r;
    */
    while (r >= y) {
        r = r - y;
        d = d + 1;
    }

    return d;
}
