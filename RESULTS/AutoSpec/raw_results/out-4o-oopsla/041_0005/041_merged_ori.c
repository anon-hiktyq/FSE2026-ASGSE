
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
  loop invariant z == k + i * (i + 1) / 2 + i + j;
  loop invariant n + k < z;
  loop invariant k + (n * (n + 1)) / 2 <= z;
  loop invariant j == i * (i - 1) / 2; // Sum of first i-1 integers;
  loop invariant j == i * (i - 1) / 2;
  loop invariant j == i * (i + 1) / 2;;
  loop invariant j == (i*(i+1))/2;
  loop invariant j == (i * (i - 1)) / 2;;
  loop invariant j == (i * (i - 1)) / 2;
  loop invariant j == (i * (i + 1)) / 2;;
  loop invariant j <= n * (n + 1) / 2;
  loop invariant i <= n;
  loop invariant i <= n + 1;;
  loop invariant i + j == i * (i + 3) / 2;
  loop invariant i * (i + 1) / 2 == j;
  loop invariant \forall integer m; 0 <= m <= i ==> j == m * (m + 1) / 2;
  loop invariant \forall integer m; 0 <= m < i ==> m + m <= z;
  loop invariant \forall integer m; 0 <= m < i ==> j >= m;
  loop invariant \exists integer m; 0 <= m < i && m + m == z;
  loop invariant 2 * n < k + i + j;
  loop invariant 1 <= k;
  loop invariant 1 <= i;
  loop invariant 0 <= j;
  loop invariant 0 < n;
  loop invariant 0 < k;
  loop invariant 0 < i;
  loop invariant j == i * (i + 1) / 2;
  loop invariant j == (i * (i + 1)) / 2; // Sum of first i integers;
  loop invariant j == (i * (i + 1)) / 2;
  loop invariant i <= n + 1;
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