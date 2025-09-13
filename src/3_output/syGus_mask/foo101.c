
void foo101(int n) {
  
    int x = 0;
    
        /* >>> LOOP INVARIANT TO FILL <<< */
        
        /*@
          loop invariant 0 <= x <= n;
          loop invariant n == \at(n, Pre);
          loop invariant x == \at(x, Pre) + \count;
          loop assigns x;
        */
        while (x < n) {
      
            x = (x + 1);
      
        }
            
}
