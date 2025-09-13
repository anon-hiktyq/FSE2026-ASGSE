#include <stdlib.h>

int sum(char n) {
    int s = 0;
    char k = 0;

    /*@
    loop invariant 0 <= k <= n + 1;
    loop invariant s == \sum(integer i; 0 <= i < k; i);
    loop invariant \forall integer i; 0 <= i < k ==> (int)i == i;
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