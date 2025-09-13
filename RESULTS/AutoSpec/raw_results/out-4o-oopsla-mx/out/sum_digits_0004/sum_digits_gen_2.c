int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant num >= 0;
    loop invariant sum == \sum{j=0..(\old(num) - num)} ((\old(num) / \pow(10, j)) % 10);
    loop invariant \forall integer j; num == 0 ==> sum == \sum{j=0..(\old(num))} ((\old(num) / \pow(10, j)) % 10);
    loop assigns num;
    loop assigns i;
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