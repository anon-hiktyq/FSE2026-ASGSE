
/*@
    requires n > 0;
    requires k > n;
    */
    
void foo015(int n, int k) {

  int j = 0;

  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant (0 < \at(n,Pre)) ==> (k == \at(k,Pre) - j);
            loop invariant (0 < \at(n,Pre)) ==> (j <= n);
            loop invariant (!(0 < \at(n,Pre))) ==> ((j == 0) && (k == \at(k,Pre)) && (n == \at(n,Pre)));
            loop invariant n == \at(n,Pre);
            loop assigns j, k;
            */
            while( j < n ) {
    j++;
    k--;
  }
             
  /*@ assert k>=0; */
}
