/*@
  requires a > 2;
*/
void hoo38(int a) {
    //algorithm searching for a divisor for factorization, by Knuth
    int r, k, q, d, n, t, s;
    
    n = s*s;
    d = a;
    r = n % d;
    t = 0;
    k = n % (d - 2);
    q = 4 * (n / (d - 2) - n / d);

    /*@
    loop invariant t == 0 || t == n % d || t == r;
    loop invariant s >= d || r != 0;
    loop invariant s >= d && r >= 0;
    loop invariant r == n % d;
    loop invariant r < d;
    loop invariant q == 4 * (n / (d - 2) - n / d);
    loop invariant q <= 4 * (n / (d - 2) - n / (d - 4));
    loop invariant q % 4 == 0;
    loop invariant n == s * s;
    loop invariant n == (d / 2) * ((d / 2) * q + 2 * r);
    loop invariant k == n % (d - 2);
    loop invariant k < d;
    loop invariant d <= s;
    loop invariant d % 2 == a % 2;
    loop invariant a <= d;
    loop invariant 8 * n == d * d * q - 2 * q * d - 4 * r * d + 4 * k * d + 8 * r;
    loop invariant 4 * (n / d - n / (d - 2)) <= q;
    loop invariant 2 < d;
    loop invariant 2 < a;
    loop invariant 0 <= t;
    loop invariant 0 <= r;
    loop invariant 0 <= q;
    loop invariant 0 <= n;
    loop invariant 0 <= k;
    loop invariant 0 < d;
    loop assigns t;
    loop assigns r;
    loop assigns q;
    loop assigns k;
    loop assigns d;
    */
    while (((s >= d) && (r != 0))) {
        if (2 * r  + q < k) {
            t = r;
            r = 2 * r - k + q + d + 2;
            k = t;
            q = q + 4;
            d = d + 2;
        } else if ((2 * r  + q >= k) && (2 * r + q < d + k + 2)) {
            t = r;
            r = 2 * r - k + q;
            k = t;
            d = d + 2;
        } else if ((2 * r  + q >= k) && (2 * r + q >= d + k + 2) && (2 * r + q < 2 * d + k + 4)) {
            t = r;
            r = 2 * r - k + q - d - 2;
            k = t;
            q = q - 4;
            d = d + 2;
        } else {
            t = r;
            r = 2 * r - k + q - 2 * d - 4;
            k = t;
            q = q - 8;
            d = d + 2;
        }
    }

    /*@ assert d * d * q - 2 * q * d - 4 * r * d + 4 * k * d + 8 * r == 8 * n; */
}