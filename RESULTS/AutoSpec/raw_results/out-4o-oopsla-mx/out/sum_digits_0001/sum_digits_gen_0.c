int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant num >= 0;
    loop invariant sum == \sum(0, \old(num), \lambda integer k; k % 10);
    loop invariant 0 <= i < 10;
    loop invariant \forall integer k; num == \old(num) / (10 ^ k);
    loop assigns num, i, sum;
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