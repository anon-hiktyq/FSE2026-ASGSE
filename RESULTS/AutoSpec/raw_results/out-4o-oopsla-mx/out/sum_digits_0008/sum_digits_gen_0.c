int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant num >= 0;
    loop invariant sum == (\sum integer k; 0 <= k < \old(num) && num == \old(num) / (10^k) % 10; k);
    loop invariant 0 <= num;
    loop assigns num;
    loop assigns sum;
    loop assigns i;
    */
    while(num>0) {
        i = num%10;
        sum += i;
        num /= 10;
    }
    return sum;
}

// write a test
void main() {
    int t = func(123);
    // @ assert t == 6;
}