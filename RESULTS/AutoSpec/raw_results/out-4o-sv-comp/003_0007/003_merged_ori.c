
int unknown1();

/*@ 
requires 0 <= n && n < 1000000;
*/
int foo003(int n) {
    int i = 0; 
    int a = 0; 
    int b = 0; 
    
   
    /*@
    loop invariant i == n ==> a + b == 3 * n;
    loop invariant i <= n;;
    loop invariant i <= b;
    loop invariant i <= a;
    loop invariant b <= a + i;
    loop invariant b <= 3 * i;
    loop invariant b <= 2 * n;
    loop invariant b <= 2 * i;;
    loop invariant b + a == 3 * i;
    loop invariant b % 3 == 2 * (i % 3);
    loop invariant b % 2 == i % 2;
    loop invariant a >= b || b >= a;
    loop invariant a <= b;
    loop invariant a <= b + i;
    loop invariant a <= 3 * i;
    loop invariant a <= 2 * n;
    loop invariant a <= 2 * i;;
    loop invariant a <= 2 * i && b <= 2 * i;
    loop invariant a + b == 3 * i;;
    loop invariant a % 3 == i % 3;
    loop invariant a % 3 == 0 || b % 3 == 0;
    loop invariant a % 3 + b % 3 == 0;
    loop invariant a % 2 == i % 2;
    loop invariant \forall integer k; 0 <= k <= i ==> a + b >= 3 * k;
    loop invariant \forall integer k; 0 <= k <= i ==> (a >= k && b >= k);
    loop invariant \forall integer k; 0 <= k < i ==> b[k] == 3;
    loop invariant \forall integer k; 0 <= k < i ==> a + b == 3 * k;
    loop invariant \forall integer k; 0 <= k < i ==> (b[k] + a[k] == 3 * k);
    loop invariant \forall integer k; 0 <= k < i ==> (b + a) / 3 == k;;
    loop invariant \forall integer k; ( 0 = x == x;; 0)=== > Z;
    loop invariant \exists integer k; 0 <= k < i && max=a[k] == B;;
    loop invariant \exists integer k; 0 <= k < i && (b[k] + a[k] == 3 * k);
    loop invariant 0 <= b;;
    loop invariant 0 <= a;;
    loop invariant 0 <= a && 0 <= b && 0 <= i;
    loop invariant i <= n;
    loop invariant b <= 2 * i;
    loop invariant a <= 2 * i;
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
