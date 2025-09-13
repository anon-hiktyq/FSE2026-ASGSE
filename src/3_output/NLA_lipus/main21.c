
int main21() {
    int x = 0;
    int y = 0;

    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant  ((y == 0)&&(x == 0)) || (x == y * y) ;
      loop invariant  y >= 0;
      loop assigns x, y;
    */
    while(unknown()) {
        y = y + 1;
        x = y * y;
    }

    /*@ assert x == y * y;*/
    return 0;
}
