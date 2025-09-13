
int unknown1();

/*@ 
requires 0 <= n && n < 1000000;
*/
int foo003(int n) {
    int i = 0; 
    int a = 0; 
    int b = 0; 
    
   
    /*@
    loop invariant 0 <= i <= n;
    loop invariant a <= 2 * n;
    loop invariant b <= 2 * n;
    loop invariant a % 3 == (i % 2 == 0 ? 0 : 1);
    loop invariant b % 3 == (i % 2 == 0 ? 0 : 2);
    loop invariant i <= n;
    loop invariant a + b == 3 * i;
    loop invariant 0 <= i;
    loop invariant 0 <= b;
    loop invariant 0 <= a;
    loop assigns i;
    loop assigns b;
    loop assigns a;
    */
    while (i < n) {
        if (unknown1()) {
            a = a + 1;
            b = b + 2;
        } else {
            a = a + 2;
            b = b + 1;
        }
        i = i + 1;
    }

    // @ assert a + b == 3 * n;*/
    
    return 0;
}
