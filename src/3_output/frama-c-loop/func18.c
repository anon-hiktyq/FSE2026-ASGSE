
void func18(int *a, int n) {
    
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant !(i < \at(n,Pre)) ==> ((n == \at(n,Pre))&&(a == \at(a,Pre)));
          loop invariant n == \at(n,Pre);
          loop invariant a == \at(a,Pre);
          loop invariant \forall integer j; 0 <= j < i ==> (j % 2 == 0 ==> a[j] == 0);
          loop invariant \forall integer j; 0 <= j < n ==> (j % 2 == 1 ==> a[j] == \at(a[j], Pre));
          loop assigns a[0..n-1];
            */
            for (int i = 0; i < n; i++) {
        if (i%2==0) 
            a[i] = 0;
    }
            
}
