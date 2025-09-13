
/*@
    requires 0 <= n;
    requires n < 1000;
    */
    
void foo0014(int n) {

    int i=0;
    int sn=0;
    
   
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant (0 <= \at(n,Pre)) ==> (0 <= i <= n + 1);
            loop invariant (0 <= \at(n,Pre)) ==> (sn == 2 * (i - 1));
            loop invariant (!(0 <= \at(n,Pre))) ==> ((sn == 0)&&(i == 0)&&(n == \at(n,Pre)));
            loop invariant n == \at(n,Pre);
            loop assigns i, sn;
            */
            for (i = 1; i <= n; i++) {
        sn = sn + (2);
    }
            
    
    /*@ assert sn == n * (2) || sn == 0; */
}
