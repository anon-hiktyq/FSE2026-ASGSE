
int hoo11(int y){
    int x = 0;

    /*@ 
      requires (x == 0) && (y == \at(y, Pre));
      assigns x;
      ensures (x % 2) == (y % 2);
    */

    /*@
      loop invariant (y == \at(y, Pre)); // y remains constant
      loop invariant (y % 2 == 0 ==> (x % 2 == 0)); // x is even if y is even
      loop assigns x;
    */
    while (x < 99) {
        if (y % 2 == 0) 
            x += 10;
        else 
            x -= 5;
    }

    /*@ assert (x % 2) == (y % 2); */
}
