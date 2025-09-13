int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant num >= 0;
    loop invariant sum == \sum(0, \old(num), \lambda integer k; k % 10) - \sum(\old(num), num, \lambda integer k; k % 10);
    loop invariant \forall integer k; num == k ==> \sum(0, k, \lambda integer x; x % 10) == sum + \sum(k, 0, \lambda integer x; x % 10);
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