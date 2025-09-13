int func(int n) {
    int sum = 0;
    int i = 0;

    /*@
    loop invariant 0 <= i <= n/2 + 1;
    loop invariant sum == 2 * (0 + 1 + 2 + ... + (i - 1)); // sum == i * (i - 1)
    loop invariant sum == i * (i - 1);
    loop assigns sum, i;
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