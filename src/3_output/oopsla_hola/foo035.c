
/*@
    requires n > 0;
    */
    
void foo035(int n) {
  int x = 0;
  
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (0 < \at(n, Pre)) ==> (0 <= x <= \at(n, Pre));
          loop invariant !(0 < \at(n, Pre) ) ==> ((x == 0) && (n == \at(n, Pre)));
          loop invariant n == \at(n, Pre);
          loop assigns x;
            */
            while(x < n) {
    x++;
  }
             
  /*@ assert (n > 0) ==> (x == n); */
 
}
