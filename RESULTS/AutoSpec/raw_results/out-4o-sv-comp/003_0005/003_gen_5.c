
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
    loop invariant a + b == 3 * i;
    loop invariant b >= a;
    loop invariant b - a == i % 2;
    loop invariant \forall integer k; 0 <= k < i ==> (unknown1() ==> a >= b) || (!unknown1() ==> b >= a);
    loop invariant \exists integer x, y; x + y == i && a == x + 2 * y && b == 2 * x + y;
    loop invariant i <= n;
    loop invariant i <= b;
    loop invariant i <= a;
    loop invariant a + b == 3 * i;
    loop invariant \exists integer x, y; x + y == i && a == x + 2 * y && b == 2 * x + y;
    loop invariant \exists integer k; 0 <= k;
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
