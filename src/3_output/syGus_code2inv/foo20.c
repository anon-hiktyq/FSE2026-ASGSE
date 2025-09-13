
void foo20(int n,int z1,int z2,int z3) {
    int x = 0;
    int m = 0;

    
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant 0 <= x <= n;
          loop invariant (0 < n) ==> (m >= 0);
          loop invariant (0 < n) ==> (m == \max(0, \at(m, Pre), x));
          loop invariant z1 == \at(z1, Pre);
          loop invariant z2 == \at(z2, Pre);
          loop invariant z3 == \at(z3, Pre);
          loop assigns x, m;
            */
            while (x < n) {

        if (unknown()) {
            m = x;
        }
        
        x = x + 1;
    }
            

    /*@ assert (n > 0) ==> (m >= 0); */

}
