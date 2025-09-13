
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
  loop invariant i <= n + 1;
  loop invariant k == 1 || k == unknown1();
  loop invariant j == i * (i - 1) / 2;
  loop invariant i <= j + n - 1;
  loop invariant \forall integer m; 0 <= m < i ==> j >= m * (m - 1) / 2; 
  loop invariant 0 <= i;
  loop invariant \forall integer m; 0 <= m < i ==> j >= m * (m + 1) / 2; 
  loop invariant i < n + 2;
  loop invariant \forall integer m; 0 <= m < i ==> j >= m * (m - 1) / 2;
  loop invariant j >= i * (i - 1) / 2;
  loop invariant j == i * (i + 1) / 2;
  loop invariant j == (i * (i + 1)) / 2;
  loop invariant i > 0 ==> j > 0;
  loop invariant i > 0 ==> j > 0 || j == 0;
  loop invariant i == 0 ==> j == 0;
  loop invariant i <= n+1;
  loop invariant i <= n + 1;
  loop invariant i <= j;
  loop invariant i < n+2;
  loop invariant i * (i - 1) / 2 <= j;
  loop invariant \forall integer x; 0 <= x <= i ==> j >= (x * (x + 1)) / 2;
  loop invariant \forall integer m; 0 <= m < i ==> j >= m * (m + 1) / 2;
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