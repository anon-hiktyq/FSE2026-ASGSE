#include <stdlib.h>

int sum(char n) {
    int s = 0;
    char k = 0;

    /*@
    loop invariant s == (k*(k-1))/2;
    loop invariant s == (k * (k - 1)) / 2;
    loop invariant s <= (n * (n + 1)) / 2;
    loop invariant n >= -1 || s >= 0;
    loop invariant k == n + 1 ==> s == (n * (n + 1)) / 2;
    loop invariant k <= n+1;
    loop invariant k <= n + 1;
    loop invariant \forall integer i; 0 <= i < k ==> 0 <= i <= n;
    loop invariant \forall char m; 0 <= m < k ==> s == (m*(m+1))/2;
    loop invariant \forall char m; 0 <= m < k ==> s == (m * (m + 1)) / 2;
    loop invariant \forall char j; 0 <= j < k ==> s == (int)(((j*(j+1))/2));
    loop invariant \forall char i; 0 <= i < k ==> s == (i * (i + 1)) / 2;
    loop invariant 0 <= s;
    loop invariant 0 <= k;
    loop assigns s;
    loop assigns k;
    */
    while(k <= n) {    
        s = s + (int)k;
        k = k + 1;
    }
    return (int)s;
}

int main() {
    int s = sum(5);
    // @ assert s == 15;
}