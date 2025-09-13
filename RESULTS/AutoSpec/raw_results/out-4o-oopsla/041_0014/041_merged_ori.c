
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
  loop invariant n < k + j;
  loop invariant k > 0 ==> z > k;
  loop invariant k < k + i + j;
  loop invariant k + (i * (i - 1)) / 2 + i <= k + i + j;
  loop invariant j == 0 || (i * (i - 1)) / 2 <= j;
  loop invariant j == (i * (i - 1)) / 2;
  loop invariant j == (i * (i + 1)) / 2;
  loop invariant j == (i * (i + 1)) / 2 - i;
  loop invariant j <= i * (i + 1) / 2;
  loop invariant i >= 0 && j >= 0;
  loop invariant i > 0 ==> j >= i;
  loop invariant i > 0 ==> j > 0;
  loop invariant i > 0 ==> j == (i * (i - 1)) / 2;
  loop invariant i == n + 1 ==> j == (n * (n + 1)) / 2;
  loop invariant i * (i + 1) / 2 == j;
  loop invariant \forall integer m; 1 <= m < i ==> j >= (m * (m - 1)) / 2;
  loop invariant \forall integer m; 0 <= m < i ==> j >= m;;
  loop invariant \forall integer m; 0 <= m < i ==> j >= m * (m + 1) / 2;
  loop invariant 2 * n <= z;
  loop invariant 2 * n < k + j + i;
  loop invariant 2 * n < k + i + j;
  loop invariant 0 <= k;
  loop invariant j == i * (i + 1) / 2;
  loop invariant i > 0 ==> j == (i * (i + 1)) / 2;
  loop invariant i == 0 || j > 0;
  loop invariant i == 0 ==> j == 0;
  loop invariant i <= n + 1;
  loop invariant \forall integer m; 0 <= m < i ==> j >= m;
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