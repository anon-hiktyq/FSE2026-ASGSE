
int fun6(int x) {
    int a = x;
    int y = 0;

    /*@
      requires x >= 0;
      ensures \result == x;
      //@ loop invariant a + y == x;
      //@ loop assigns y, a;
      //@ loop variant a;
    */
    while(a != 0) {
        y = y + 1;
        a = a - 1;
    }
    
    return y;
}

int goo6() {
    int num = fun6(3);
    return 0;
}
