int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant sum == \sum{j=0..(\old(num) - num)} ((\old(num) / \pow(10, j)) % 10);
    loop invariant sum == \sum(0..i-1, (num_copy % \pow(10, j)) / \pow(10, j-1));
    loop invariant sum == \sum(0, \old(num), \lambda integer k; k % 10);
    loop invariant sum == \sum(0, \old(num)) of digits;
    loop invariant sum == \sum(0, \old(num) / (10^k) % 10) for k in {0, ..., \log10(\old(num))};
    loop invariant sum == \sum(0, \floor(\log10(num) + 1), (num / \pow(10, \floor(\log10(num) - x))) % 10);
    loop invariant sum == \old(sum) + (\old(num) - num) % 10;
    loop invariant sum == \old(sum) + (\old(num) - num) % 10 + (\old(num) / 10 == 0 ? \old(num) % 10 : 0);
    loop invariant num == \old(num) / (10^(\log10(\old(num)) - \log10(num)));
    loop invariant i < 10;
    loop invariant \forall integer k; num == k ==> sum == \sum(0 <= i < k && i % 10);;
    loop invariant \forall integer k; num == \sum digits of num and num >= digits;
    loop invariant \forall integer k; num == 123;
    loop invariant \forall integer k; k >= 0 ==> sum == \sum(0, k, (num div 10));
    loop invariant \forall integer k; 0 <= k <= \old(num) ==> sum == sum + k % 10;
    loop invariant \forall integer k; 0 <= k < i ==> sum == sum + k;
    loop invariant \forall integer j; num == 0 ==> sum == \sum{j=0..(\old(num))} ((\old(num) / \pow(10, j)) % 10);
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