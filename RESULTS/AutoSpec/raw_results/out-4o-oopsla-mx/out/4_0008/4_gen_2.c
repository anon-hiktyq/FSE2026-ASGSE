#include <stdio.h>
#include <math.h>

/*@
requires n >= 0;
ensures \result == (pow(2.0, n + 1) - 1);
assigns \nothing;
*/
int fun(int n) {
    double y = 0;
    double i = 0;

    while(i <= n) {
        y = y + pow(2.0, i);
        i = i + 1;
    }
    return y;
}

int main() {
    int res = fun(4);
    //@assert res == 7;
}