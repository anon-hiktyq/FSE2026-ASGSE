#include <stdlib.h>

int sum(char n) {
    int s = 0;
    char k = 0;

    /*@
    loop invariant 0 <= k <= n + 1;
    loop invariant s == \sum(0, k - 1, \lambda integer i; i);
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