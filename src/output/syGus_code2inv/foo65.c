
void foo65(int y) {
    int x = 1;
    
    
    
    
            
        /*@
          loop invariant  y >= 0 || (x == 1 && y == \at(y, Pre));
          loop invariant  x >= 1 && x <= 101;
          loop assigns x, y;
            */
            while (x <= 100) {
        y = 100 - x;
        x = x + 1;
    }
            

    /*@ assert (y >= 0); */

}
