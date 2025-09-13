
int unknown1();

/*@ 
requires 0 <= n && n < 1000000;
*/
int foo003(int n) {
    int i = 0; 
    int a = 0; 
    int b = 0; 
    
   
    /*@
    loop invariant i; <= b;
    loop invariant i; <= a;
    loop invariant i == (a + b) / 3;
    loop invariant b == 2 * a - i;
    loop invariant b <= 2 * n;
    loop invariant b - a == i || a - b == i;
    loop invariant b - a == i % 2;
    loop invariant b % 3 == i % 3;;
    loop invariant a >= b || b >= a;
    loop invariant a == 2 * b - i;
    loop invariant a <= b;
    loop invariant a <= 2 * n;
    loop invariant a - b == i || b - a == i;
    loop invariant a - b == i % 3;
    loop invariant a % 3 == i % 3;;
    loop invariant a % 3 == b % 3;
    loop invariant \forall integer x; 0 <= x <= i ==> (2 * a - b == x || 2 * b - a == x);
    loop invariant \forall integer k; 0 <= k <= i ==> a + b >= 3 * k;
    loop invariant \forall integer k; 0 <= k <= i ==> a + b == 3 * k;
    loop invariant \forall integer k; 0 <= k <= i ==> (a + b) % 3 == 0;
    loop invariant \forall integer k; 0 <= k < i ==> a + b >= k * 3;
    loop invariant \forall integer k; 0 <= k < i ==> (a >= b || b >= a);
    loop invariant \forall integer k; 0 <= k < i ==> (a > b ? a - b <= i - k : b - a <= i - k);
    loop invariant \forall integer k; 0 <= k < i ==> (a + b) % 3 == 0;
    loop invariant \forall integer k; 0 <= k < i ==> ((a == 2 * b - i) || (b == 2 * a - i));
    loop invariant \exists integer x; 0 <= x <= i && b - a == 2 * x - i;
    loop invariant \exists integer k; 0 <= k <= i && 2 * k + (i - k) == b && k + 2 * (i - k) == a;;
    loop invariant 0 <= a && 0 <= b && 0 <= i;
    loop invariant (a + b) % 3 == 0;
    loop invariant (a + b) % 2 == i % 2;
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
