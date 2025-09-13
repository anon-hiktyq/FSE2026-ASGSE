
int func(int *a, int n, int x, int *sum) {
    int p = 0;
    int count = 0;
    *sum = 0;

  
    /*@
    loop invariant p <= n;
    loop invariant count == \sum_{k=0}^{p-1} (a[k] == x);
    loop invariant count == \sum_{i=0}^{p-1} (a[i] == x);
    loop invariant count == \sum_{i=0}^{p-1} (a[i] == x ? 1 : 0);
    loop invariant \forall integer k; 0 <= k < p ==> (a[k] == x ==> count == count + 1);
    loop invariant 0 <= p;
    loop invariant 0 <= count;
    loop invariant *sum == x * count;
    loop invariant *sum == count * x;;
    loop invariant *sum == count * x;
    loop invariant *sum == \sum_{i=0}^{p-1} (a[i] == x ? x : 0);
    loop assigns p;
    loop assigns count;
    loop assigns *sum;
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
   
    return count;
}

// write a test
void main() {
    int arr[5] = {1, 2, 3, 4, 5};
    int sum = 0;
    int count = func(arr, 5, 3, &sum);
  
}