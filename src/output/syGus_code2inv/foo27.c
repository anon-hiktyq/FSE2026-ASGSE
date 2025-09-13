
void foo27(int n) {

    int x = n;
    
    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant (\at(n,Pre) > 1) ==> (x == \at(n,Pre) - (\at(n,Pre) - x)); 
      loop invariant (!(\at(n,Pre) > 1)) ==> ((x == \at(n,Pre))&&(n == \at(n,Pre)));
      loop invariant n == \at(n,Pre);
      loop invariant (\at(n,Pre) >= 1) ==> (x >= 1); // Weakened invariant to hold under initial conditions
      loop assigns x;
    */
    while (x > 1) {
        x = x - 1;
    }
    
    /*@ assert (n >= 1) ==> (x == 1); */
}
