
/*@
axiomatic Sum_invariant {
    logic integer sum_count(integer x, integer y, integer c);
    axiom sum_initial:
        \forall integer x, integer y, integer c; x == c && y == 0 ==> sum_count(x, y, c) == c;
    axiom sum_preservation:
        \forall integer x, integer y, integer c; x + y == c ==> sum_count(x, y, c) == c;
}
*/

/*@
requires c >= 0;
ensures \result == c;
*/
int func8(int c) {
    int x = c;
    int y = 0;

    /*@
      loop invariant (\at(c,Pre) > 0) ==> (x + y == \at(c,Pre));
      loop invariant (\at(c,Pre) > 0) ==> (y >= 0);
      loop invariant (!(\at(c,Pre) > 0)) ==> ((y == 0)&&(x == \at(c,Pre))&&(c == \at(c,Pre)));
      loop invariant c == \at(c,Pre);
    */
    while (x > 0) {
        x = x - 1;
        y = y + 1;
    }

    return y;
}
