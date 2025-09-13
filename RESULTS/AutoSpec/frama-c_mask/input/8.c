#include <limits.h>


int add(int *p, int *q) {
    return *p + *q;
}

int main() {
    int a = 24;
    int b = 32;
    int x;

    x = add(&a, &b) ;
 

    x = add(&a, &a) ;
  
}