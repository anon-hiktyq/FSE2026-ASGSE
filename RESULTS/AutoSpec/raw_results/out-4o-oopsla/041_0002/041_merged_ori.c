
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
  loop invariant z == k + i + j;;
  loop invariant z == k + i + j;
  loop invariant z == k + (i * (i + 1)) / 2 + i;
  loop invariant k > 0 ==> z >= k + i * (i + 1) / 2 + i > 2;;
  loop invariant k + n < k + i + j;
  loop invariant k + n * (n - 1) / 2 < z;
  loop invariant k + j <= z;
  loop invariant j >= i && i <= n + 1;
  loop invariant j == (i * (i - 1)) / 2; // Sum of first (i-1) natural numbers;
  loop invariant j == (i * (i - 1)) / 2; // Sum of first (i-1) natural numbers.;
  loop invariant j == (i * (i - 1)) / 2; // Sum of first (i - 1) natural numbers;
  loop invariant j == (i * (i - 1)) / 2;
  loop invariant j == (i * (i + 1)) / 2;;
  loop invariant j <= n * (n + 1) / 2;
  loop invariant j <= (n * (n + 1)) / 2; // Sum of first n natural numbers.;
  loop invariant j <= (i * (i + 1)) / 2;;
  loop invariant i; <= z;
  loop invariant i >= 0 && i <= n + 1;
  loop invariant i == n + 1 ==> j == (n * (n + 1)) / 2;
  loop invariant i <= j;
  loop invariant i + j <= z;
  loop invariant i * (i + 1) / 2 <= j;
  loop invariant \forall integer x; 0 <= x <= i ==> j >= x * (x + 1) / 2;
  loop invariant \forall integer x; 0 <= x < i ==> j >= x;
  loop invariant \forall integer x; 0 <= x < i ==> j >= (x * (x + 1)) / 2;
  loop invariant \forall integer x; 0 <= x < i ==> j == (x * (x + 1)) / 2 + (i - x) * (x + 1);
  loop invariant \forall integer p; 1 <= p <= i ==> j >= p * (p - 1) / 2;
  loop invariant 1 <= k;
  loop invariant 1 <= i;
  loop invariant 0 <= j;
  loop invariant (i >= 1) ==> j == (i - 1) * i / 2;
  loop invariant j == i * (i + 1) / 2;
  loop invariant j == (i * (i + 1)) / 2; // Sum of first i natural numbers;
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