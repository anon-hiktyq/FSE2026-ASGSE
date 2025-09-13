#include <limits.h>

/*@
requires \valid(p) && \valid(q);
requires INT_MIN <= *p + *q <= INT_MAX;
requires *q >= INT_MIN && *q <= INT_MAX;
requires *p >= INT_MIN && *p <= INT_MAX;
requires *p <= INT_MAX - *q;
requires *p <= INT_MAX - *q && *p >= INT_MIN - *q; // No overflow;
requires *p <= INT_MAX - *q && *p >= INT_MIN - *q;
requires *p <= INT_MAX - *q && *p >= INT_MIN + *q;;
requires (long)*p + (long)*q <= INT_MAX && (long)*p + (long)*q >= INT_MIN;
ensures \result == *p + *q;
assigns \nothing;
*/
int add(int *p, int *q) {
    return *p + *q;
}

int main() {
    int a = 24;
    int b = 32;
    int x;

    x = add(&a, &b) ;
    // @ assert x == a + b ;
    // @ assert x == 56 ;

    x = add(&a, &a) ;
    // @ assert x == a + a ;
    // @ assert x == 48 ;
}