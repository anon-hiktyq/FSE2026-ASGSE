int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant num >= 0;
    loop invariant sum == (\sum integer k; 0 <= k < (\old(num) - num)/10; (\old(num) / (10^(k+1))) % 10);
    loop invariant \forall integer k; 0 <= k < (\old(num) - num)/10 ==> sum == (\old(num) / (10^(k+1))) % 10 + sum;
    loop assigns i;
    loop assigns num;
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