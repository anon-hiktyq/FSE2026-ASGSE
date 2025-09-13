#include <limits.h>


/*@
requires \valid(a) && \valid(b) && \valid(r);
requires INT_MIN <= *a <= INT_MAX;
requires INT_MIN <= *b <= INT_MAX;
requires INT_MIN <= *r <= INT_MAX;
ensures \result == *a + *b + *r;
assigns \nothing;
*/
int add(int *a, int *b, int *r) {
    return *a + *b + *r;
}

int main() {
    int a = 24;
    int b = 32;
    int r = 12;
    int x;

    x = add(&a, &b, &r) ;

    x = add(&a, &a, &a) ;
}