int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant num >= 0;
    loop invariant sum == \sum(0, \old(num)) of digits;
    loop invariant sum >= 0;
    loop invariant \forall integer k; num == \sum digits of num and num >= digits;
    loop assigns i, sum, num;
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