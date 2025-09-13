
/*@
    requires n >= 0; 
    requires k >= 0;
    */
    
void foo94(int n,int k) {
  
    int i = 0;
    int j = 0;
    
    
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              loop invariant (\at(n, Pre) >= 0 && \at(k, Pre) >= 0) ==> ((0 <= \at(n, Pre)) ==> (0 <= i <= n + 1));
              loop invariant (\at(n, Pre) >= 0 && \at(k, Pre) >= 0) ==> ((0 <= \at(n, Pre)) ==> (j == (i * (i + 1)) / 2));
              loop invariant (\at(n, Pre) >= 0 && \at(k, Pre) >= 0) ==> ((!(0 <= \at(n, Pre))) ==> ((j == 0)&&(i == 0)&&(k == \at(k, Pre))&&(n == \at(n, Pre))));
              loop invariant (\at(n, Pre) >= 0 && \at(k, Pre) >= 0) ==> (k == \at(k, Pre));
              loop invariant (\at(n, Pre) >= 0 && \at(k, Pre) >= 0) ==> (n == \at(n, Pre));
              loop assigns i, j;
            */
            while (i <= n) {
      
       i  = i + 1;
       j  = j + i;
      
  
    }
            
  
  }
