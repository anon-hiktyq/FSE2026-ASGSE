
int unknown1();

/*@ 
requires 0 <= n && n < 1000000;
*/
int foo003(int n) {
    int i = 0; 
    int a = 0; 
    int b = 0; 
    
   
    /*@
    loop invariant i <= a + b;
    loop invariant b <= 2*i;
    loop invariant b <= 2 * i;
    loop invariant a >= b || b >= a;
    loop invariant a <= 2*i;
    loop invariant a <= 2 * i;
    loop invariant a + b == 3*i;
    loop invariant \forall integer k; 0 <= k < i ==> a + b >= 3*k;
    loop invariant \forall integer k; 0 <= k < i ==> (a + b - 3 * k) % 3 == 0;
    loop invariant \forall integer j; 0 <= j < i ==> a + b == 3 * i;
    loop invariant \exists integer k; 0 <= k < i ==> a + b == 3*k;
    loop invariant 3 * i == a + b;
    loop invariant 2*i - n <= b;
    loop invariant 2*i - n <= a;
    loop invariant 0 <= a && 0 <= b;
    loop invariant i <= n;
    loop invariant i <= b;
    loop invariant i <= a;
    loop invariant a + b == 3 * i;
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

    //@ assert a + b == 3 * n;*/
    
    return 0;
}
