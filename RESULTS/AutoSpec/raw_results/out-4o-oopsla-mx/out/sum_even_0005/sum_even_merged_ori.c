int func(int n) {
    int sum = 0;
    int i = 0;

    /*@
    loop invariant sum == i * (i - 1);
    loop invariant sum == 2 * \sum(0, i-1, \lambda integer k; k);
    loop invariant sum == 2 * (i * (i - 1)) / 2;
    loop invariant sum == 2 * ((i - 1) * i) / 2; // sum of first (i-1) even numbers;
    loop invariant sum == 2 * ((i - 1) * i) / 2; // Sum of the first (i-1) even numbers;
    loop invariant sum == 2 * ((i - 1) * i) / 2;
    loop invariant sum == 2 * ((i - 1) * i / 2);
    loop invariant i <= n/2 + 1;
    loop invariant \forall integer k; 0 <= k < i ==> sum == 2 * (k * (k + 1) / 2);
    loop invariant 0 <= i;
    loop assigns sum;
    loop assigns i;
    */
    while(i <= n/2) {
        sum = sum + 2*(i);
        i++;
    }
    return sum;
}

// write a test
void main() {
    int t = func(10);
    // @ assert t == 30;
}