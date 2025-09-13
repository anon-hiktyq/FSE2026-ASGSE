
/*@
    requires n > 0;
    */
    
void foo037(int n) {
  int x = 0;
  int m = 0;
 
  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant (0 < \at(n,Pre)) ==> (0 <= x <= n);
            loop invariant (0 < \at(n,Pre)) ==> (((m == 0)&&(x == 0)&&(n == \at(n,Pre))) || (0 <= m < n));
            loop invariant !(0 < \at(n,Pre) ) ==> ((m == 0)&&(x == 0)&&(n == \at(n,Pre)));
            loop invariant n == \at(n,Pre);
            loop assigns x, m;
            */
            while (x < n) {
    if (unknown()) {
      m = x;
    }
    x = x + 1;
  }
            
  /*@ assert (n > 0) ==> (0 <= m && m < n); */
}
