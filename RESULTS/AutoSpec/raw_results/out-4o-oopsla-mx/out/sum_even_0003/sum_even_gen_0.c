int func(int n) {
    int sum = 0;
    int i = 0;

    /*@
    loop invariant 0 <= i <= n/2 + 1;
    loop invariant sum == 2 * ((i - 1) * i) / 2;
    loop invariant sum == \sum(0 <= k < i, 2 * k);
    loop assigns i;
    loop assigns sum;
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