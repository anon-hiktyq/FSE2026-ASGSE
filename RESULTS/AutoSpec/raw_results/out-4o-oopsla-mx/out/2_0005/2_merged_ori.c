#include <stdlib.h>

int sum(char n) {
    int s = 0;
    char k = 0;

    /*@
    loop invariant s == \sum(integer i; 0 <= i < k; i);
    loop invariant s == \sum(0, k - 1, \lambda integer i; i);
    loop invariant s == (k * (k - 1)) / 2;
    loop invariant s == (\sum integer i; 0 <= i < k; i);
    loop invariant k <= n + 1;
    loop invariant \forall integer i; 0 <= i < k ==> (int)i == i;
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