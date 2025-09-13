#include <stdlib.h>

/*@
requires n >= 0;
assigns \nothing;
*/
int sum(char n) {
    int s = 0;
    char k = 0;

    /*@
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
    //@ assert s == 15;
}