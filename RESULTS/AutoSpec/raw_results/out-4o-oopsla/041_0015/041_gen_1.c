
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
  loop invariant k + (i * (i - 1)) / 2 + i <= z;  
  loop invariant 0 <= i <= n + 1;  
  loop invariant j == (i * (i + 1)) / 2;  
  loop invariant z == k + i + j;  
  loop invariant z >= k + j;  
  loop invariant z >= k + i;  
  loop invariant z > n;  
  loop invariant z >= 0;  
  loop invariant i > 0 ==> z >= k + (i * (i + 1)) / 2 + 1;
  loop invariant k + (i * (i - 1)) / 2 + i <= k + i + j;
  loop invariant j == i * (i + 1) / 2;
  loop invariant j == 0 || (i * (i - 1)) / 2 <= j;
  loop invariant j == (i * (i + 1)) / 2;
  loop invariant j <= i * (i + 1) / 2;
  loop invariant i >= 0 && j >= 0;
  loop invariant i > 0 ==> j >= i;
  loop invariant i > 0 ==> j > 0;
  loop invariant i > 0 ==> j == (i * (i + 1)) / 2;
  loop invariant i == 0 || j > 0;
  loop invariant i == 0 ==> j == 0;
  loop invariant i <= n + 1;
  loop invariant i * (i + 1) / 2 == j;
  loop invariant \forall integer m; 1 <= m < i ==> j >= (m * (m - 1)) / 2;
  loop invariant \forall integer m; 0 <= m < i ==> j >= m;
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