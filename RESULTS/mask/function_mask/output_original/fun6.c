
int fun6(int x) {
    int a = x;
    int y = 0;

    /*@
      requires x >= 0;
      ensures \result == x;
      //@ loop invariant (\at(x,Pre) != 0) ==> (a == \at(x,Pre) - y);
      //@ loop invariant (\at(x,Pre) != 0) ==> (y == \at(x,Pre) - a);
      //@ loop invariant !(\at(x,Pre) != 0) ==> ((y == 0) && (a == \at(x,Pre)) && (x == \at(x,Pre)));
      //@ loop invariant x == \at(x,Pre);
      //@ loop assigns y, a;
      //@ loop variant a;
    */
    while(a != 0) {
        y = y + 1;
        a = a - 1;
    }
    
    return y;
}
