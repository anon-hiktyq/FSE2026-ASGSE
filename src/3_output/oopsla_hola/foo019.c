
/*@
    requires n >= 0;
    requires m >= 0;
    requires m < n;
    */
    
void foo019(int n, int m) {
 
  int x = 0; 
  int y = m;
 
  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (0 < \at(n,Pre)) ==> (0 <= x <= n);
          loop invariant (0 < \at(n,Pre)) ==> (y == \at(m,Pre) + (x > \at(m,Pre) ? (x - \at(m,Pre)) : 0));
          loop invariant (!(0 < \at(n,Pre))) ==> ((y == \at(m,Pre))&&(x == 0)&&(m == \at(m,Pre))&&(n == \at(n,Pre)));
          loop invariant m == \at(m,Pre);
          loop invariant n == \at(n,Pre);
          loop assigns x, y;
            */
            while(x < n) {
    x++;
    if(x > m) y++;
  }
            
  /*@ assert y==n; */
}
