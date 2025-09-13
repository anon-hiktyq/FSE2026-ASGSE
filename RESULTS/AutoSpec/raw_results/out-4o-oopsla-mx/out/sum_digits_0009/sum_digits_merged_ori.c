/*@
requires num >= 0;;
requires num >= 0;
ensures num == 0 ==> \result == 0;
ensures \result >= 0;
ensures \result == \sum(0..(\numofdigits(num)-1), \lambda integer k; (num / (10^k)) % 10);
ensures \result == \sum(0, \old(num), \lambda integer i; (i % 10));
ensures \result == \sum(0, \numofdigits(num)-1, \lambda integer k; (num / \pow(10, k)) % 10);
ensures \result == \sum(0, \numofdigits(num)-1, \lambda integer i; (num / \pow(10, i)) % 10);
ensures \result == \sum(0, \num_length(num) - 1, \lambda integer k; (num / (int)pow(10, k)) % 10);;
ensures \result == \sum(0, \log10(num) + 1, (num / (int)\pow(10, \lambda)) % 10);
ensures \result == \sum(0, \floor(\log10(num)) + 1, \lambda integer k; (num / (int)\pow(10, k)) % 10);
ensures \exists integer n; n >= 0 && num == \sum(0, n, \lambda integer k; (int)(\pow(10, k) * ((\result / \pow(10, k)) % 10)));
assigns \nothing;;
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