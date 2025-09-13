int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant num >= 0;
    loop invariant sum == \sum(0..(\old(num) - num)) % 10;
    loop invariant \forall integer k; 0 <= k <= \old(num) ==> sum == \sum(0..k) % 10;
    loop invariant sum >= 0;
    loop assigns num;
    loop assigns i;
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