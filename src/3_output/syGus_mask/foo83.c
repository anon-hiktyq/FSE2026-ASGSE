
void foo83(int y) {

    int x = -5000;
  
    /*@
      loop invariant x < 0 || x >= 0;
      loop assigns x, y;
    */
    while (x < 0) {
      
      x  = x + y;
      y  = y + 1;
  
    }
}
