/*@
requires num >= 0;
ensures \result >= 0;
ensures \result == \sum(0..\floor(\log10(num)+1), \lambda integer k; (num / (int)pow(10,k)) % 10);
ensures \result == \sum(0..(\num_digits(num)-1), \lambda integer k; (num / \pow(10, k)) % 10);
ensures \result == \sum(0, \numofdigits(num), \lambda integer k; (num / (10^k)) % 10);
ensures \result == \sum(0, \floor(\log10(num) + 1), \lambda integer k; (num / (10^k)) % 10);
ensures \result == \sum(0 .. \numofdigits(num)-1, (\floor(num / \pow(10, \iterator)) % 10));
ensures \result == (\sum integer i; 0 <= i < sizeof(num) * CHAR_BIT && (num / (10^i)) % 10 >= 0; (num / (10^i)) % 10);
ensures \result == (\sum integer i; 0 <= i < \strlen(\int_to_string(num)) && num > 0; num % 10);
ensures \result == (\sum integer i; 0 <= i < 10 && num / (10^i) > 0; (num / (10^i)) % 10);
assigns \nothing;
*/
int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant i >= 0 && i < 10;
    loop invariant 0 <= sum;
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