int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant sum == \sum(0..\old(num)) (num % 10);
    loop invariant sum == \sum(0..(\old(num) - num)) (int)((\old(num)/10^k) % 10);
    loop invariant sum == \sum(0..(\old(num) - num)) % 10;
    loop invariant sum == \sum(0, \old(num), \lambda integer k; (k % 10));
    loop invariant sum == \sum(0, \old(num), (num % 10));
    loop invariant sum == \sum(0, \old(num) - num, (int k) (\old(num) / pow(10, k) % 10));
    loop invariant sum == \sum integer k; 0 <= k < i ==> (num / (10^k)) % 10;
    loop invariant sum == \old(sum) + i;
    loop invariant sum == (\sum integer k; 0 <= k < \old(num) / (10^k) % 10);
    loop invariant i == num % 10;
    loop invariant i < 10;
    loop invariant \forall integer k; num == (\old(num) / 10^k);
    loop invariant \forall integer k; num / (10^k) == 0 ==> sum == (\sum integer j; 0 <= j < k; \old(num) / (10^j) % 10);
    loop invariant \forall integer k; k >= num ==> k / 10 == \old(k) / 10;
    loop invariant \forall integer k; k >= 0 ==> sum >= 0;
    loop invariant \forall integer k; k >= 0 ==> i == num % 10;
    loop invariant \forall integer k; 0 <= k <= \old(num) ==> sum == \sum(0..k) % 10;
    loop invariant \forall integer k; 0 <= k <= \old(num) ==> sum == \sum(0, k, (num % 10));
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