int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant num >= 0;
    loop invariant sum == \sum(0 <= k < \old(num) && \old(num)/\pow(10, k) > 0, (\old(num)/\pow(10, k)) % 10);
    loop invariant \forall integer k; num == \old(num)/\pow(10, k) && num % 10 == \old(num)/\pow(10, k) % 10;
    loop assigns i;
    loop assigns sum;
    loop assigns num;
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