
/*@
axiomatic Division {
    logic integer quotient(integer x, integer y);
    logic integer remainder(integer x, integer y);

    axiom quotient_definition:
        \forall integer x, integer y; y > 0 ==> x == quotient(x, y) * y + remainder(x, y);

    axiom remainder_bounds:
        \forall integer x, integer y; y > 0 ==> 0 <= remainder(x, y) < y;
}
*/

/*@
requires y > 0;
requires x >= 0;
ensures \result == quotient(x, y); // The result is the quotient of x divided by y
ensures remainder(x, y) == x - \result * y; // Explicitly define the remainder
ensures 0 <= remainder(x, y) < y; // Ensures the remainder is within bounds
*/
int goo2(int x, int y) {
    int r = x;
    int d = 0;

    /*@
      loop invariant r == \at(x,Pre) - d * y; // Relationship between r, d, x, and y
      loop invariant 0 <= r < y || r >= y; // r is either less than y or will be reduced further
      loop invariant d == quotient(\at(x,Pre), y) - quotient(r, y); // Relationship between d and quotient
      loop invariant y == \at(y,Pre); // y remains unchanged
      loop invariant x == \at(x,Pre); // x remains unchanged
      loop assigns r, d; // Variables modified in the loop
      loop variant r; // r decreases with each iteration
    */
    while (r >= y) {
        r = r - y;
        d = d + 1;
    }

    return d;
}
