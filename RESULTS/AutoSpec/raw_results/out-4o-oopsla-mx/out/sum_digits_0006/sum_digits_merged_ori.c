int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant sum == \sum(0, \old(num), k % 10) where k is the digits processed so far;
    loop invariant sum == \sum(0, \old(num), \lambda integer k; k % 10);
    loop invariant sum == \sum(0, \old(num), \lambda integer k; k % 10) - \sum(\old(num), num, \lambda integer k; k % 10);
    loop invariant sum == \sum(0, \old(num), \lambda integer k; (k % 10));
    loop invariant sum == \sum(0, \old(num) - num, k, k % 10);
    loop invariant sum == \sum(0, \num_of_digits(num), digit_sum(num));
    loop invariant sum == \sum(0 <= k < \old(num) && \old(num)/\pow(10, k) > 0, (\old(num)/\pow(10, k)) % 10);
    loop invariant i >= 0 && i < 10;
    loop invariant \forall integer k; num == k ==> \sum(0, k, \lambda integer x; x % 10) == sum + \sum(k, 0, \lambda integer x; x % 10);
    loop invariant \forall integer k; num == \old(num)/\pow(10, k) && num % 10 == \old(num)/\pow(10, k) % 10;
    loop invariant \forall integer k; num == \old(num) / (\pow(10, k));
    loop invariant \forall integer k; k >= num ==> sum == \sum(0, \old(num) - k, m, m % 10);
    loop invariant \forall integer k; k >= num ==> k % 10 == i;
    loop invariant \forall integer k; k >= 0 && k <= \old(num) ==> num == \old(num) / (10 ^ k);
    loop invariant \forall integer k; 0 <= k <= i ==> digit_sum(i);
    loop invariant \forall integer k; 0 <= k < \old(num) ==> k % 10 >= 0 && k % 10 <= 9;
    loop invariant 0 <= sum;
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