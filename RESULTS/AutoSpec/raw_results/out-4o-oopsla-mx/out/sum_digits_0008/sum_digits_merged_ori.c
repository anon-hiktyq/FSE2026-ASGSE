int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant sum == num ==> num;
    loop invariant sum == loop assigns i;
    loop invariant sum == \sum(0..num) sum + num[append];
    loop invariant sum == \sum(0..num) (num % 10 + (num /10);
    loop invariant sum == \sum(0, \old(num), k % 10) where k represents the digits of the original num;
    loop invariant sum == \sum(0, \old(num), \lambda integer k; k % 10);
    loop invariant sum == \sum integer k; 0 <= k < \old(num) && \old(num) / (10^k) > 0 ==> (\old(num) / (10^k)) % 10;
    loop invariant sum == (\sum integer k; 0 <= k < \old(num) && num == \old(num) / (10^k) % 10; k);
    loop invariant sum == (\sum integer k; 0 <= k < (\old(num) - num)/10; (\old(num) / (10^(k+1))) % 10);
    loop invariant loop assigns num;
    loop invariant \forall integer k; num == \old(num) / (10 ^ k);
    loop invariant \forall integer k; k >= num ==> sum == \sum(0, k, \lambda integer x; x % 10);
    loop invariant \forall integer k; 0 <= k < sum ==> k == k % 10;
    loop invariant \forall integer k; 0 <= k < \old(num) ==> sum >= k % 10;;
    loop invariant \forall integer k; 0 <= k < (\old(num) - num)/10 ==> sum == (\old(num) / (10^(k+1))) % 10 + sum;
    loop invariant 0 <= num;
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