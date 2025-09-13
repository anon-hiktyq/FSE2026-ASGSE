/*@
requires num >= 0;
ensures \result >= 0;
ensures \result == \sum(0..\num_digits(num)-1, \lambda integer k; (num / (10^k)) % 10);
ensures \result == \sum(0..\floor(log10(num)+1), \lambda integer k; (num / (10^k)) % 10);
ensures \result == \sum(0..(\length(num)-1), \lambda integer k; (num / (10^k)) % 10);
ensures \result == \sum(0, num_digits(num) - 1, (num / (10 ^ \index)) % 10);;
ensures \result == \sum(0, \floor(log10(num)) + 1, \lambda integer k; (num / (10^k)) % 10);
ensures \result == \sum(0, \floor(\log10(num)+1), \lambda integer k; (num / (10^k)) % 10);
ensures \result == \sum(0, \floor(\log10(num) + 1), (num / \pow(10, \lambda)) % 10);
ensures \forall integer i; 0 <= i < 10 ==> \result == \sum(0, num, k % 10);
assigns \nothing;
*/
int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
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