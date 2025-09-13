/*@
requires num >= 0;
ensures \result >= 0;
ensures \result == \sum(0, \old(num), \lambda integer i; (i % 10));
ensures num == 0 ==> \result == 0;
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