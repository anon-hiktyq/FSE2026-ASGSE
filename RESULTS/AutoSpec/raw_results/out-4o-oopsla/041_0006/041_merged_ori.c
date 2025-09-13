
/*@
ensures \result >= 0;
*/
int unknown();



/*@
requires n > 0;
*/
void foo041(int n, int flag) {
  int k = 1;
  if (flag) {
    k = unknown1();
  }
  int i = 0, j = 0;
  /*@
  loop invariant z == k + i + j;
  loop invariant k == 1 || (k > 0 && j >= i * (i + 1) / 2);
  loop invariant j == (i * (i - 1)) / 2;
  loop invariant j == (i * (i + 1)) / 2; // sum of first i integers;
  loop invariant j <= n * (n + 3) / 2;
  loop invariant j <= n * (n + 3) / 2 || j <= n * (n + 1) / 2;
  loop invariant j <= n * (n + 3) / 2 || i <= n;
  loop invariant j <= n * (n + 3) / 2 || i * j <= n * (n + 3) / 2;
  loop invariant j <= n * (n + 3) / 2 || 1 <= k;
  loop invariant j <= n * (n + 3) / 2 || 0 <= k;
  loop invariant j <= n * (n + 3) / 2 || 0 <= i * (i + 1) / 2;
  loop invariant j <= n * (n + 3) / 2 || 0 <= _j;
  loop invariant j <= n * (n + 1) / 2;
  loop invariant j <= n * (n + 1) / 2 || 0 <= k;
  loop invariant j <= n * (n + 1) / 2 || 0 <= _j;
  loop invariant j < n * (n + 3) / 2;
  loop invariant j < n * (n + 1) / 2;
  loop invariant i <= n;
  loop invariant i <= n || j <= n * (n + 1) / 2;
  loop invariant i <= n || 1 <= k;
  loop invariant i <= n || 0 <= k;
  loop invariant i <= n || 0 <= i * (i + 1) / 2;
  loop invariant i <= n || 0 <= _j;
  loop invariant i < n;
  loop invariant i + j == k + i * (i + 3) / 2;
  loop invariant i + j == i * (i + 1) / 2;
  loop invariant i + j == (i + 1) * i / 2;
  loop invariant i * j <= n * (n + 3) / 2;
  loop invariant i * j <= n * (n + 3) / 2 || j <= n * (n + 1) / 2;
  loop invariant i * j <= n * (n + 3) / 2 || i <= n;
  loop invariant i * j <= n * (n + 3) / 2 || 1 <= k;
  loop invariant i * j <= n * (n + 3) / 2 || 0 <= k;
  loop invariant i * j <= n * (n + 3) / 2 || 0 <= i * (i + 1) / 2;
  loop invariant i * j <= n * (n + 3) / 2 || 0 <= _j;
  loop invariant i * j < n * (n + 3) / 2;
  loop invariant i * (i + 1) / 2 <= j;
  loop invariant i * (i + 1) / 2 <= j || j <= n * (n + 3) / 2;
  loop invariant i * (i + 1) / 2 <= j || j <= n * (n + 1) / 2;
  loop invariant i * (i + 1) / 2 <= j || i <= n;
  loop invariant i * (i + 1) / 2 <= j || i * j <= n * (n + 3) / 2;
  loop invariant i * (i + 1) / 2 <= j || 1 <= k;
  loop invariant i * (i + 1) / 2 <= j || 0 <= k;
  loop invariant i * (i + 1) / 2 <= j || 0 <= i * (i + 1) / 2;
  loop invariant i * (i + 1) / 2 <= j || 0 <= _j;
  loop invariant i * (i + 1) / 2 < j;
  loop invariant \forall integer m; 0 <= m < i ==> j >= m + n;
  loop invariant \forall integer m; 0 <= m < i ==> j >= m + i;
  loop invariant \forall integer m; 0 <= m < i ==> j >= m * (m - 1) / 2;
  loop invariant \forall integer m; 0 <= m < i ==> j >= m * (m + 1) / 2;
  loop invariant \forall integer m; 0 <= m < i ==> j >= (m * (m + 1)) / 2;
  loop invariant \forall integer k; 0 <= k < i ==> j >= k;
  loop invariant \exists integer m; 0 <= m <= i && j == (m * (m + 1)) / 2;
  loop invariant 1 <= k;
  loop invariant 1 <= k || j <= n * (n + 1) / 2;
  loop invariant 1 <= k || 0 <= k;
  loop invariant 1 <= k || 0 <= _j;
  loop invariant 1 < k;
  loop invariant 0 <= k;
  loop invariant 0 <= k || 0 <= _j;
  loop invariant 0 <= i * (i + 1) / 2;
  loop invariant 0 <= i * (i + 1) / 2 || j <= n * (n + 1) / 2;
  loop invariant 0 <= i * (i + 1) / 2 || 1 <= k;
  loop invariant 0 <= i * (i + 1) / 2 || 0 <= k;
  loop invariant 0 <= i * (i + 1) / 2 || 0 <= _j;
  loop invariant 0 <= _j;
  loop invariant 0 < k;
  loop invariant 0 < i * (i + 1) / 2;
  loop invariant 0 < _j;
  loop invariant (i*(i+1))/2 + j == 2 * j;
  loop invariant (\exists integer m; 0 <= m < i && j == m*(m+1)/2);
  loop invariant j == i * (i + 1) / 2;
  loop invariant j == (i*(i+1))/2;
  loop invariant j == (i * (i + 1)) / 2; // Sum of first i integers;
  loop invariant j == (i * (i + 1)) / 2;
  loop invariant i <= n + 1;
  loop invariant i + j == i * (i + 3) / 2;
  loop invariant i * (i + 1) / 2 == j;
  loop invariant \forall integer m; 0 <= m < i ==> j >= m;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant 0 < n;
  loop assigns j;
  loop assigns i;
  */
  while (i <= n) {
    i++;
    j += i;
  }
  int z = k + i + j;
  // @ assert z > 2 * n;
}