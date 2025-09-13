#include <stdlib.h>

int sum(char n) {
    int s = 0;
    char k = 0;

    /*@
    loop invariant 0 <= k <= n + 1;
    loop invariant s == (k * (k - 1)) / 2;
    loop invariant \forall char x; 0 <= x < k ==> s == \sum(0, k - 1, x);
    loop assigns k, s;
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