int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant num >= 0;
    loop invariant sum == \sum(0, \old(num) / (10^k) % 10) for k in {0, ..., \log10(\old(num))};
    loop invariant num == \old(num) / (10^(\log10(\old(num)) - \log10(num)));
    loop invariant \forall integer k; num == 123;
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