
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
  loop invariant i * (i - 1) / 2 <= j;
  loop invariant j <= i * (i + 1) / 2;
  loop invariant i <= n;
  loop invariant 0 <= i <= n + 1;
  loop invariant j >= 0;
  loop invariant j >= i;
  loop invariant (2 * j) >= i * (i + 1);
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