
void arrayDouble(int *a, unsigned int n) {
    int p = 0;


    /*@
    loop invariant p <= n;
    loop invariant 0 <= p;
    loop assigns p;
    loop assigns a[0..n-1];
    */
    while (p < n) {
        a[p] = a[p] * 2;
        p = p + 1;
    } 
}

int main() {
    int arr[] = {0,1,2,3,4,5};
    arrayDouble(arr, 6);
 
}