
/*@
    requires l > 0;
    requires n > l;
    */
    
void foo03(int n, int l) {
  int i, k;

  k = 1;
  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              loop invariant (!(1 < \at(n,Pre))) ==> ((k == 1) && (l == \at(l,Pre)) && (n == \at(n,Pre)));
              loop assigns k, i;
            */
            for (k = 1; k < n; k++) {
    i = l;

    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant l <= i <= n; // Modified invariant
      loop invariant i >= l;
      loop invariant i == l + (i - l);
    */
    for (; i < n; i++) {
    }
    
  }
            
  /*@ assert \forall integer i; (l <= i < n) ==> (1 <= i); */
}
