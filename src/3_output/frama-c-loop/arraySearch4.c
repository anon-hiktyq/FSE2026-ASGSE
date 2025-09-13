
int arraySearch4(int *a, int x, int n) {
    int p = 0;

    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant (0 < \at(n,Pre)) ==> (0 <= p <= \at(n,Pre));
            loop invariant !(0 < \at(n,Pre)) ==> ((p == 0) && (n == \at(n,Pre)) && (x == \at(x,Pre)) && (a == \at(a,Pre)));
            loop invariant n == \at(n,Pre);
            loop invariant x == \at(x,Pre);
            loop assigns p;
            */
            while (p < n) {
        if (a[p] == x) {
            return 1;
        }
        p++;
    }
            
    return 0;
}
