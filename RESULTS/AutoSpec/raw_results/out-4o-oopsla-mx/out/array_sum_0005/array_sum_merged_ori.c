/*@
requires n >= 0;
requires \valid(a + (0..n-1));
ensures n == 0 ==> \result == 0;
ensures \result == \sum(0, n-1, a[\lambda]);
ensures \result == \sum(0, n-1, a[\lambda integer i; i]);
ensures \result == \sum(0, n-1, a[\lambda i; i]);
ensures \result == \sum(0, n-1, a[\lambda i; a[i]]);
ensures \result == \sum(0, n-1, a);
ensures \result == \sum(0, n-1, \lambda integer i; a[i]);
assigns \nothing;
*/
int sumArray(int *a, int n) {
    int p = 0, sum = 0;

    /*@
    loop invariant 0 <= p;
    loop assigns sum;
    loop assigns p;
    */
    while (p < n) {
        sum = sum + a[p];
        p++;
    }
    return sum;
}

// write a test
void main() {
    int arr[5] = {1, 2, 3, 4, 5};
    int sum = sumArray(arr, 5);
    // @ assert sum == 15;
}