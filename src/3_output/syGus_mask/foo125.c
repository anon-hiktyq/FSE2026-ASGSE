
void foo125(int x, int y) {

    int i = x;
    int j = y;
    
    /*@
      loop invariant (\at(x,Pre) != 0) ==> (x == i - (j - y));
      loop invariant (\at(x,Pre) != 0) ==> (y == j - (i - x));
      loop invariant (!(\at(x,Pre) != 0)) ==> ((j == \at(y,Pre))&&(i == \at(x,Pre))&&(y == \at(y,Pre))&&(x == \at(x,Pre)));
      loop invariant j == \at(y,Pre);
      loop invariant i == \at(x,Pre);
      loop assigns x, y;
    */
    while (x != 0) {
        x = x - 1;
        y = y - 1;
    }
}
