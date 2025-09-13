
/*@
    requires 0 <= n && n < 1000000;
    */
    
int foo003(int n) {
    int i = 0; 
    int a = 0; 
    int b = 0; 
    
   
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (0 < \at(n,Pre)) ==> (0 <= i <= \at(n,Pre));
          loop invariant (0 < \at(n,Pre)) ==> (a + b == 3 * i);
          loop invariant (!(0 < \at(n,Pre))) ==> ((b == 0)&&(a == 0)&&(i == 0)&&(n == \at(n,Pre)));
          loop invariant n == \at(n,Pre);
          loop assigns a, b, i;
            */
            while (i < n) {
        if (unknown1()) {
            a = a + 1;
            b = b + 2;
        } else {
            a = a + 2;
            b = b + 1;
        }
        i = i + 1;
    }
            

    /*@ assert a + b == 3 * n;*/
    
    return 0;
}
