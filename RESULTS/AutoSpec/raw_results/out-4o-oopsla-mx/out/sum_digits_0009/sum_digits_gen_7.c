/*@
requires num >= 0;
ensures \result >= 0;
ensures \result == \sum(0, \log10(num) + 1, (num / (int)\pow(10, \lambda)) % 10);
assigns \nothing;
*/
int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
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