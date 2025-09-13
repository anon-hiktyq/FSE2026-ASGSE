
int hoo15(){
    int x = 0;
    int y = 0;

    /*@
      loop invariant x == 4 * y;
      loop invariant y >= 0; // y is non-negative since it starts at 0 and only increments
      loop assigns x, y; // x and y are the variables being modified in the loop
    */
    while (unknown()) {
        x += 4;
        y++;
    }

    //post-condition
    /*@ assert x == 4 * y; */
}
