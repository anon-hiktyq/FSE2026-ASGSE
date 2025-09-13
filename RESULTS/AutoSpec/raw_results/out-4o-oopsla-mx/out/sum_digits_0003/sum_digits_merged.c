int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant sum <= 10*i;
    loop invariant i == num % 10;
    loop invariant i <= sum;
    loop invariant i <= 9;
    loop invariant i <= 10;
    loop invariant \forall integer k; num >= 10 ==> sum == sum + k %10;
    loop invariant \forall integer k; 0 <= k <= i ==> sum >= k;
    loop invariant \forall integer k; 0 <= k < i ==> sum >= k;
    loop invariant \forall integer k; 0 <= k < i ==> (num / (10^k)) % 10 >= 0;
    loop invariant 0 <= num;
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