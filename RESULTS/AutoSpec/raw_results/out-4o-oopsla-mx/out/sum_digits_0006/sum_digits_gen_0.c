int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant num >= 0;
    loop invariant sum == \sum(0, \old(num) - num, k, k % 10);
    loop invariant \forall integer k; k >= num ==> sum == \sum(0, \old(num) - k, m, m % 10);
    loop assigns i;
    loop assigns num;
    loop assigns sum;
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