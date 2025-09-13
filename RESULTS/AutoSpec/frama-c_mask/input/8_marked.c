#include <limits.h>


/* 1. FUNC CONTRACT */
int add(int *p, int *q) {
    return *p + *q;
}

/* 2. FUNC CONTRACT */
int main() {
    int a = 24;
    int b = 32;
    int x;

    x = add(&a, &b) ;
 

    x = add(&a, &a) ;
  
}