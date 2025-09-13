int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant sum == \sum(0, num_initial - num, \lambda integer k; (num_initial / (10^k) % 10));
    loop invariant sum == \sum(0, i, \old(num) % 10);
    loop invariant sum == \sum(0, \old(num)-num, \i -> (\old(num) / (10^i) % 10));
    loop invariant sum == \sum(0, \old(num), num % 10);
    loop invariant sum == \sum(0, \old(num), \lambda integer k; k % 10);
    loop invariant sum == \sum(0, \old(num), (num % 10));
    loop invariant sum == \sum(0, \old(num) > 0 ? \old(num) % 10 : 0);
    loop invariant i < 10;
    loop invariant \forall integer k; num >= 0 ==> sum == \sum(0,k,(num%10));
    loop invariant \forall integer k; num > 0 ==> sum == (sum+i);
    loop invariant \forall integer k; num == \old(num) / (10 ^ k);
    loop invariant \forall integer k; k >= 0 ==> sum == \sum(0, k, \old(num) %10 );
    loop invariant \forall integer k; k >= 0 && num == \old(num)/10^k ==> sum == \sum(0, k, \i -> (\old(num) / (10^i) % 10));
    loop invariant \forall integer k; 0 <= k <= sum ==> sum == (sum + num);;
    loop invariant \forall integer k; 0 <= k < i ==> t == func(k);
    loop invariant \forall integer k; 0 <= k < \old(num) ==> num == \old(num)/(\pow(10, k));
    loop invariant 0 <= sum;
    loop invariant 0 <= num;
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