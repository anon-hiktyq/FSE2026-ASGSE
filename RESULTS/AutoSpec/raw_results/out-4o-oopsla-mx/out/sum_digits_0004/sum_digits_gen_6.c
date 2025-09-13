int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant num >= 0;
    loop invariant sum == \sum(0, \floor(\log10(num) + 1), (num / \pow(10, \floor(\log10(num) - x))) % 10);
    loop invariant 0 <= i < 10;
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