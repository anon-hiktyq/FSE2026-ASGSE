
/*@
axiomatic Division {
    logic integer quotient(integer x, integer y);
    logic integer remainder(integer x, integer y);

    axiom division_properties:
        \forall integer x, integer y; y > 0 ==> 
        x == quotient(x, y) * y + remainder(x, y) && 
        0 <= remainder(x, y) < y;
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
assigns *r;
*/
int fun1(int x, int y, int *r) {
    *r = x;
    int d = 0;

    /*@
    loop invariant 0 <= *r;
    loop invariant *r == \at(x,Pre) - d * y;
    loop invariant d == quotient(\at(x,Pre), y);
    loop invariant *r == remainder(\at(x,Pre), y);
    loop invariant y > 0;
    loop assigns *r, d;
    loop variant *r;
    */
    while (*r >= y) {
        *r = *r - y;
        d = d + 1;
    }

    return d;
}

/*@ 
requires \true;
ensures \true;
*/
int goo1() {
    int a = 3;
    int num = fun1(1, 2, &a);
    return 0;
}
