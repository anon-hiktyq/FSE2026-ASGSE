int func(int n) {
    int sum = 0;
    int i = 0;

    /*@
    loop invariant 0 <= i <= n/2 + 1;
    loop invariant sum == 2 * ((i - 1) * i) / 2; // Sum of even numbers till 2*(i-1)
    loop assigns i, sum;
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