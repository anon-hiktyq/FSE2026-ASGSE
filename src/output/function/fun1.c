
/*@
axiomatic Division {
    logic integer quotient(integer x, integer y);
    logic integer remainder(integer x, integer y);

    axiom division_properties:
        \forall integer x, integer y; y > 0 ==> x == quotient(x, y) * y + remainder(x, y) && 0 <= remainder(x, y) < y;
}
*/

/*@
requires y > 0;
requires \valid(r);
requires *r == x;
ensures \result == quotient(x, y);
ensures *r == remainder(x, y);
ensures x == \result * y + *r;
ensures 0 <= *r < y;
assigns *r, \result;
*/
int fun1(int x, int y, int *r) {
    *r = x;
    int d = 0;

    /*@
    loop invariant (\at(*r,Pre) >= \at(y,Pre)) ==> (*r == \at(*r,Pre) - d * \at(y,Pre));
    loop invariant (\at(*r,Pre) >= \at(y,Pre)) ==> (d == (\at(*r,Pre) - *r) / \at(y,Pre));
    loop invariant y == \at(y,Pre);
    loop invariant x == \at(x,Pre);
    loop invariant \at(*r,Pre) == \at(x,Pre);
    loop assigns *r, d;
    loop variant *r;
    */
    while (*r >= y) {
        *r = *r - y;
        d = d + 1;
    }

    return d;
}
