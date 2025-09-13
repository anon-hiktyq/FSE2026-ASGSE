int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant num >= 0;
    loop invariant sum == \sum(0, \old(num), k % 10) where k is the digits processed so far;
    loop invariant \forall integer k; k >= 0 && k <= \old(num) ==> num == \old(num) / (10 ^ k);
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