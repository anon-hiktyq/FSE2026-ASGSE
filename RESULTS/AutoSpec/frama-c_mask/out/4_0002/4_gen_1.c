#include<limits.h>


int test(int x) {
    int a = x;
    int y = 0;


    /*@
    loop invariant y >= 0;
    loop invariant y + a == x;
    loop invariant a >= 0;
    loop assigns y;
    loop assigns a;
    */
    while(a != 0) {
        y = y + 1;
        a = a - 1;
    }
    return y;
}
    
int main() {
    int num = test(3);
    return 0;
}