
int check(int *a, int *b, int n) {
    
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant !(i < \at(n,Pre)) ==> ((n == \at(n,Pre))&&(b == \at(b,Pre))&&(a == \at(a,Pre)));
          loop invariant n == \at(n,Pre);
          loop invariant b == \at(b,Pre);
          loop invariant a == \at(a,Pre);
          loop invariant \forall integer j; 0 <= j < i ==> b[j] == \at(b,Pre)[j];
          loop invariant \forall integer j; 0 <= j < i ==> a[j] == \at(a,Pre)[j];
          loop assigns i;
            */
            for (int i = 0; i < n; i++) {
        if (a[i] != b[i]) {
            return 0;
        }
    }
            
    return 1;
}
