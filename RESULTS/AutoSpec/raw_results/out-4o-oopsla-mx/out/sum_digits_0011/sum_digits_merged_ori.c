/*@
requires num >= 0;
ensures \result >= 0;
ensures \result == \sum(num);
ensures \result == \sum(0..num_digits-1, (num / (10 ^ i)) % 10), where num_digits is the number of digits in num;
ensures \result == \sum(0..\num_length(num)-1, num / 10^k % 10);
ensures \result == \sum(0, \num_elements(num), \lambda integer d; d == num % 10);
ensures \result == \sum(0, \num_digits(num)-1, i, (num / (10^i)) % 10);
ensures \result == \sum(0, \floor(\log10(num)), \lambda integer k; (num / \pow(10, k)) % 10);
ensures \result == \sum(0, \floor(\log10(num) + 1), \lambda integer k; (num / (10^k)) % 10);
ensures \result == (\sum integer i; 0 <= i < \num_digits(num); (num / (10^i)) % 10);
assigns \nothing;
*/
int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant i < 10;
    loop invariant \forall integer k; k >= 0 ==> sum >= 0;
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