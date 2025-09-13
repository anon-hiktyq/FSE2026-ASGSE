int func(int *a, int n, int x, int *sum) {
    int p = 0;
    int count = 0;
    *sum = 0;

    /*@
    loop invariant p <= n;
    loop invariant count == \sum(0, p-1, a[k] == x ? 1 : 0);
    loop invariant count == \sum(0, p-1, \lambda int k; a[k] == x ? 1 : 0);
    loop invariant count == \sum(0, p-1, (a[k] == x ? 1 : 0));
    loop invariant count == \sum(0, p-1, (a[\lambda] == x ? 1 : 0));
    loop invariant \forall integer k; 0 <= k < p ==> (a[k] == x) ==> (\exists integer j; 0 <= j < count && a[j] == x);
    loop invariant \forall integer k; 0 <= k < p ==> (a[k] == x ? count-- : count);
    loop invariant \forall integer k; 0 <= k < p ==> (a[k] == x ? (*sum == count * x) : (*sum == count * x));
    loop invariant \forall integer k; 0 <= k < p ==> (a[k] == x ==> \at(*sum, Here) >= x);
    loop invariant \forall integer k; 0 <= k < p ==> (a[k] == x ==> *sum >= x);
    loop invariant \forall integer k; 0 <= k < p ==> (a[k] == x <==> (count > 0 && *sum == count * x));
    loop invariant \forall integer i; 0 <= i < p ==> (a[i] == x ==> \at(*sum, LoopEntry) + x * count == *sum);
    loop invariant 0 <= p;
    loop invariant 0 <= count;
    loop invariant *sum == count * x;
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
    // @ assert \at(*sum, Label_a) == count*x;
    return count;
}

// write a test
void main() {
    int arr[5] = {1, 2, 3, 4, 5};
    int sum = 0;
    int count = func(arr, 5, 3, &sum);
    // @ assert sum == count*3;
}