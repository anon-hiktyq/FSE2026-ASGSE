
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
  loop invariant j == i * (i - 1) / 2;
  loop invariant j == (i * (i + 1)) / 2;;
  loop invariant j <= i * (i + 1) / 2;
  loop invariant j <= (i - 1) * i / 2 + i;
  loop invariant i == n + 1 ==> j == (n * (n + 1) / 2 + n + 1);
  loop invariant i == (j - i) / i + 1;
  loop invariant i == (j - i * (i + 1) / 2) / (i + (i + 1) / 2);
  loop invariant i <= n;
  loop invariant i <= j;
  loop invariant i < z;
  loop invariant i * (i - 1) / 2 <= j;
  loop invariant i * (i + 1) <= (2 * j);
  loop invariant \forall integer m; 0 <= m < i ==> j >= m;;
  loop invariant 1 <= k;
  loop invariant 0 < i;
  loop invariant j == i * (i + 1) / 2;
  loop invariant j == (i * (i + 1)) / 2;
  loop invariant i <= n + 1;
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