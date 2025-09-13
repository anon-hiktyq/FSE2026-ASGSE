


/*@
axiomatic Sum_axiom {
    logic integer sum(integer x, integer y);
    axiom sum_identity:
        \forall integer x, y; sum(x, y) == x + y;
}
*/

/*@
requires x >= 0;
ensures \result == x;
*/
int test(int x) {
    int a = x;
    int y = 0;

    /*@ 
      loop invariant (\at(x,Pre) != 0) ==> (y + a == \at(x,Pre));
      loop invariant (\at(x,Pre) != 0) ==> (y == \at(x,Pre) - a);
      loop invariant (!(\at(x,Pre) != 0)) ==> ((y == 0)&&(a == \at(x,Pre))&&(x == \at(x,Pre)));
      loop invariant x == \at(x,Pre);
    */
    while(a != 0) {
        y = y + 1;
        a = a - 1;
    }
            
    return y;
}

int goo7() {
    int num = test(3);
    //@ assert num == 3;
    return 0;
}


