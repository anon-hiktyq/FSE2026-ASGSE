
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
  loop invariant k <= j/n || i * (i - 1) / 2 <= j;
  loop invariant j == i * (i - 1) / 2;
  loop invariant j == (i * (i - 1)) / 2;
  loop invariant j <= n * (n + 1) / 2;
  loop invariant j <= n * (n + 1) / 2 || k <= j/n;
  loop invariant j <= n * (n + 1) / 2 || i * (i - 1) / 2 <= j;
  loop invariant j <= n * (n + 1) / 2 || 2 * n < k + i + j;
  loop invariant j < n * (n + 1) / 2;
  loop invariant i >= 1 && i <= n + 1;
  loop invariant i >= 0 && j >= 0;
  loop invariant i == n ==> j == (n * (n + 1)) / 2;
  loop invariant i == n + 1 ==> j == n * (n + 1) / 2;
  loop invariant i == j/k;
  loop invariant i <= n;
  loop invariant i <= n || k <= j/n;
  loop invariant i <= n || j <= n * (n + 1) / 2;
  loop invariant i <= n || i * (i - 1) / 2 <= j;
  loop invariant i <= n || 2 * n < k + i + j;
  loop invariant i <= n || 1 <= i;
  loop invariant i <= n || 0 <= k * i / 2;
  loop invariant i < n;
  loop invariant i * (i - 1) / 2 <= j;
  loop invariant i * (i - 1) / 2 < j;
  loop invariant i * (i - 1) / 2 < j;
  loop invariant i * (i - 1) / 2 < j;
  loop invariant i * (i - 1) / 2 < j;
  loop invariant i * (i - 1) / 2 < j;
  loop invariant i * (i - 1) / 2 < j;
  loop invariant i * (i - 1) / 2 < j;
  loop invariant i * (i - 1) / 2 < j;
  loop invariant i * (i - 1) / 2 < j;
  loop invariant i * (i - 1) / 2 < j;
  loop invariant i * (i - 1) / 2 < j;
  loop invariant i * (i - 1) / 2 < j;
  loop invariant i * (i - 1) / 2 < j;
  loop invariant i * (i - 1) / 2 < j;
  loop invariant i * (i - 1) / 2 < j;
  loop invariant i * (i - 1) / 2 < j;
  loop invariant i * (i + 1) / 2 == j;
  loop invariant \forall integer x; 1 <= x <= i ==> j >= x * (x - 1)/2 + k;
  loop invariant \forall integer x; 0 <= x < i ==> j >= x + k;
  loop invariant \forall integer x; 0 <= x < i ==> j >= (x * (x + 1)) / 2 + i;
  loop invariant \forall integer p; 1 <= p <= i ==> j == p * (p - 1) / 2 + i;
  loop invariant \forall integer m; 0 <= m < i ==> j >= (m * (m + 1)) / 2;
  loop invariant \exists integer x; 0 <= x < i && j == (x * (x + 1)) / 2;
  loop invariant 2 * n <= k + i + j;
  loop invariant 2 * n < k + i + j;
  loop invariant 2 * n < k + i + j || i * (i - 1) / 2 <= j;
  loop invariant 1 <= k;
  loop invariant 1 <= k || k <= j/n;
  loop invariant 1 <= k || j <= n * (n + 1) / 2;
  loop invariant 1 <= k || i <= n;
  loop invariant 1 <= k || i * (i - 1) / 2 <= j;
  loop invariant 1 <= k || 2 * n < k + i + j;
  loop invariant 1 <= k || 1 <= i;
  loop invariant 1 <= k || 0 <= k;
  loop invariant 1 <= k || 0 <= k * i / 2;
  loop invariant 1 <= k || 0 < i;
  loop invariant 1 <= i;
  loop invariant 1 <= i || k <= j/n;
  loop invariant 1 <= i || j <= n * (n + 1) / 2;
  loop invariant 1 <= i || i * (i - 1) / 2 <= j;
  loop invariant 1 <= i || 2 * n < k + i + j;
  loop invariant 1 <= i || 0 <= k * i / 2;
  loop invariant 1 < k;
  loop invariant 1 < i;
  loop invariant 0 <= k;
  loop invariant 0 <= k || k <= j/n;
  loop invariant 0 <= k || j <= n * (n + 1) / 2;
  loop invariant 0 <= k || i <= n;
  loop invariant 0 <= k || i * (i - 1) / 2 <= j;
  loop invariant 0 <= k || 2 * n < k + i + j;
  loop invariant 0 <= k || 1 <= i;
  loop invariant 0 <= k || 0 <= k * i / 2;
  loop invariant 0 <= k * i / 2;
  loop invariant 0 <= k * i / 2 || k <= j/n;
  loop invariant 0 <= k * i / 2 || j <= n * (n + 1) / 2;
  loop invariant 0 <= k * i / 2 || i * (i - 1) / 2 <= j;
  loop invariant 0 <= k * i / 2 || 2 * n < k + i + j;
  loop invariant 0 < k;
  loop invariant 0 < k * i / 2;
  loop invariant 0 < i;
  loop invariant 0 < i || k <= j/n;
  loop invariant 0 < i || j <= n * (n + 1) / 2;
  loop invariant 0 < i || i <= n;
  loop invariant 0 < i || i * (i - 1) / 2 <= j;
  loop invariant 0 < i || 2 * n < k + i + j;
  loop invariant 0 < i || 1 <= i;
  loop invariant 0 < i || 0 <= k;
  loop invariant 0 < i || 0 <= k * i / 2;
  loop invariant j >= i && i <= n + 1;
  loop invariant j == i * (i + 1) / 2;
  loop invariant j == (i * (i + 1)) / 2; // Sum of first i natural numbers;
  loop invariant j == (i * (i + 1)) / 2;
  loop invariant i >= 0 && i <= n + 1;
  loop invariant i <= n + 1;
  loop invariant i <= j;
  loop invariant i * (i + 1) / 2 <= j;
  loop invariant \forall integer x; 0 <= x < i ==> j >= x;
  loop invariant \forall integer x; 0 <= x < i ==> j >= (x * (x + 1)) / 2;
  loop invariant \forall integer p; 1 <= p <= i ==> j >= p * (p - 1) / 2;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
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