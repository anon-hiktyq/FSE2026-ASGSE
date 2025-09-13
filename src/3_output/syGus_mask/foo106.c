
/*@
    requires a <= m;
    requires j < 1;
    */
    
void foo106(int m,int j,int a) {

    int k = 0;
    
        /*@
          loop invariant  (\at(j,Pre) < 1 && \at(a,Pre) <= \at(m,Pre)) ==> (((k == 0)&&(a == \at(a,Pre))&&(j == \at(j,Pre))&&(m == \at(m,Pre))) || (m >= a && m >= \at(m,Pre))) ;
          loop invariant  (\at(j,Pre) < 1 && \at(a,Pre) <= \at(m,Pre)) ==> (k >= 0 && k <= 1) ;
          loop invariant (\at(j,Pre) < 1 && \at(a,Pre) <= \at(m,Pre)) ==> (a == \at(a,Pre));
          loop invariant (\at(j,Pre) < 1 && \at(a,Pre) <= \at(m,Pre)) ==> (j == \at(j,Pre));
          loop assigns m, k;
            */
        while ( k < 1) {

        if(m < a) {
            m = a;
        }
        
        k = k + 1;
    }
}
