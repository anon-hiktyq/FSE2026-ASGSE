#include <stdlib.h>

/*@
requires n >= 0 && n <= CHAR_MAX;
ensures \result == (n * (n + 1)) / 2;
assigns \nothing;
*/
int sum(char n) {
    int s = 0;
    char k = 0;

    /*@
    loop invariant \forall integer i; 0 <= i < k ==> (int)i == i;
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