int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant sum == \sum(0..i)(num % 10);
    loop invariant sum == \sum(0, i-1, \lambda k; (num / (10^k)) % 10);
    loop invariant sum == \sum(0, i-1, \lambda k; (num / (10^(k+1))) % 10);
    loop invariant sum == \sum(0, \original(num), i -> (i % 10));
    loop invariant sum == \sum(0, \old(num)-num, \old(num) % 10);
    loop invariant sum == \sum(0, \old(num), k % 10);;
    loop invariant sum == \sum(0, \old(num), k % 10);
    loop invariant sum == (\sum integer k; 0 <= k <= i ==> k);
    loop invariant sum <= \sum(0, i-1, \lambda k; 9);
    loop invariant sum <= \original(num);
    loop invariant sum <= 10*i;
    loop invariant num == \old(num)/(10^i);
    loop invariant num == \old(num) / \pow(10, i);
    loop invariant num == \old(num) / (10^i);
    loop invariant i == num % 10;
    loop invariant i <= sum;
    loop invariant i <= 9;
    loop invariant i <= 10;
    loop invariant i < 10;;
    loop invariant \forall integer k; num >= 10 ==> sum == sum + k %10;
    loop invariant \forall integer k; num == \original(num) / (10^k);
    loop invariant \forall integer k; num == 0 ==> sum == (\sum integer k; 0 <= k < 10 ==> k);
    loop invariant \forall integer k; 0 <= k <= i ==> sum >= k;
    loop invariant \forall integer k; 0 <= k <= \old(num) ==> num <= \old(num);
    loop invariant \forall integer k; 0 <= k < i ==> sum >= k;
    loop invariant \forall integer k; 0 <= k < i ==> (num / (10^k)) % 10 >= 0;
    loop invariant \forall integer k; 0 <= k < \old(num) ==> sum >= k;
    loop invariant 0 <= num;
    loop invariant (sum +=i %10) <= \forall integer i; num;
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