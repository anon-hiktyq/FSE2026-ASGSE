
int sumArray(int *a, int n) {
    int p = 0, sum = 0;

    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              loop invariant 0 <= p && p <= n;
              loop invariant sum == \sum_{i=0}^{p-1} a[i];
              loop variant n - p;
            */
            while (p < n) {
        sum = sum + a[p];
        p++;
    }
            
    return sum;
}
