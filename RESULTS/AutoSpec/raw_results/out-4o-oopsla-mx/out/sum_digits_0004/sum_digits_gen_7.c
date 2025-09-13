int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant num >= 0;
    loop invariant sum == \old(sum) + (\old(num) - num) % 10 + (\old(num) / 10 == 0 ? \old(num) % 10 : 0);
    loop invariant \forall integer k; num == k ==> sum == \sum(0 <= i < k && i % 10); 
    loop assigns sum, num, i;
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