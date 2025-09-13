
/*@
    requires n > 0;
    */
    
void foo67(int n) {
  int x = 0;
  int m = 0;
 
            
        /* >>> LOOP INVARIANT FILLED <<< */
        
            /*@
          loop invariant (0 < \at(n,Pre)) ==> (0 <= x <= n);
          loop invariant (0 < \at(n,Pre)) ==> (((m == 0)&&(x == 0)&&(n == \at(n,Pre))) || (0 <= m < x));
          loop invariant (!(0 < \at(n,Pre))) ==> ((m == 0)&&(x == 0)&&(n == \at(n,Pre)));
          loop invariant n == \at(n,Pre);
          loop assigns x, m;
          loop variant n - x;
            */
            while (x < n) {
    if (unknown()) {
      m = x;
    }
    x = x + 1;
  }
    /*@ assert (n > 0) ==> (0 <= m && m < n); */
            
  /* mask_1 */
}
