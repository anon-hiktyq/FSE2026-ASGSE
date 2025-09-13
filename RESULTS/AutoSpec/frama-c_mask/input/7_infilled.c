#include <limits.h>


/* @ >>> INFILL <<< */
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