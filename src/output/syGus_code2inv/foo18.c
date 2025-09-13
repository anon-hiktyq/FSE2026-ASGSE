
void foo18(int n) {
    int x = 1;
    int m = 1;
    
    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant n >= 1 ==> (1 <= x <= n); // x is within valid bounds when n >= 1
      loop invariant (1 < n) ==> (m >= 1); // Ensure m is at least 1 if n > 1
      loop assigns x, m; // x and m are modified by the loop
    */
    while (x < n) {
        
        if (unknown()) {
            m = x;
        }
        
        x = x + 1;
    }
            
    /*@ assert (n > 1) ==> (m >= 1); */
}
