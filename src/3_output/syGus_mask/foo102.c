
void foo102(int n) {
  
    int x = 0;
    
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              loop invariant (0 < \at(n,Pre)) ==> (x <= n);
              loop invariant (!(0 < \at(n,Pre))) ==> ((x == 0) && (n == \at(n,Pre)));
              loop invariant n == \at(n,Pre);
              loop assigns x;
            */
            while (x < n) {
      
      x  = (x + 1);
      
    }
            
    
  }
