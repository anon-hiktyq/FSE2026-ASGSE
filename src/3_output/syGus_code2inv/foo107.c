
void foo107(int m,int j,int a) {

    int k = 0;
    
    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant 0 <= k <= 1;
      loop invariant \at(a, Pre) <= \at(m, Pre) ==> (m >= a);
      loop invariant (k == 0) ==> (m == \at(m, Pre) || m == a);
      loop invariant (k == 1) ==> (m >= a);
      loop invariant \at(a, Pre) <= \at(m, Pre) ==> (a == \at(a, Pre));
      loop invariant \at(a, Pre) <= \at(m, Pre) ==> (j == \at(j, Pre));
      loop assigns m, k;
    */
    while ( k < 1) {

        if(m < a) {
            m = a;
        }
        
        k = k + 1;
    }
            
    /*@ assert a <= m; */

}
