int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant num >= 0;
    loop invariant sum == \sum(0, \old(num)-num, \old(num) % 10);
    loop invariant \forall integer k; 0 <= k <= i ==> sum >= k;
    loop invariant i >= 0;
    loop invariant i <= 9;
    loop invariant \forall integer k; 0 <= k <= \old(num) ==> num <= \old(num);
    loop invariant i < 10;
    loop invariant 0 <= sum;
    loop invariant 0 <= i;
    loop assigns sum;
    loop assigns num;
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