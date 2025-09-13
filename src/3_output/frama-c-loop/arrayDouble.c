
void arrayDouble(int *a, unsigned int n) {
    int p = 0;

    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (0 < \at(n,Pre)) ==> (0 <= p <= \at(n,Pre));
          loop invariant !(0 < \at(n,Pre)) ==> ((p == 0)&&(n == \at(n,Pre))&&(a == \at(a,Pre)));
          loop invariant n == \at(n,Pre);
          loop invariant a == \at(a,Pre);
          loop invariant \forall integer i; 0 <= i < p ==> a[i] == \at(a[i], Pre) * 2;
          loop invariant \forall integer i; p <= i < n ==> a[i] == \at(a[i], Pre);
          loop assigns p, a[0..n-1];
            */
            while (p < n) {
        a[p] = a[p] * 2;
        p = p + 1;
    }
             
}
