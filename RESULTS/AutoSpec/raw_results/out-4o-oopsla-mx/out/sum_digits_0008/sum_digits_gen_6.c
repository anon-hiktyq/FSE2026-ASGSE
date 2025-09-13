int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant num >= 0;
    loop invariant sum == \sum(0..num) (num % 10 + (num /10)
    loop invariant sum == \sum(0..num) sum + num[append];
    loop invariant sum == loop assigns i;
    loop invariant loop assigns num;
    loop invariant sum ==  num ==> num;
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