/*@
requires n >= 0;
ensures \result == (n / 2) * (n / 2 + 1);
assigns \nothing;
*/
int func(int n) {
    int sum = 0;
    int i = 0;

    /*@
    loop invariant sum == i * (i - 1);
    loop invariant sum == 2 * (i * (i - 1)) / 2; // sum of first (i - 1) even numbers;
    loop invariant sum == 2 * (i * (i - 1)) / 2; // Sum of first (i-1) even numbers;
    loop invariant sum == 2 * ((i - 1) * i) / 2;
    loop invariant sum == 2 * ((i * (i - 1)) / 2);
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