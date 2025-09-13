
int func3(int *a, int n, int x, int *sum) {
    int p = 0;
    int count = 0;
    *sum = 0;

    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant 0 <= p && p <= n;
            loop invariant count == \sum_{i=0}^{p-1} (a[i] == x ? 1 : 0);
            loop invariant *sum == count * x;
            loop assigns p, count, *sum;
            loop variant n - p;
            */
            while (p < n) {
        if (a[p] == x) {
            count = count + 1;
            *sum = *sum + x;
        }
        p = p + 1;
    }
            
    Label_a:
    *sum += 0;
    //@ assert \at(*sum, Label_a) == count * x;
    return count;
}
