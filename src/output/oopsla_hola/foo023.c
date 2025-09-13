
/*@
requires n >= 0;
ensures \result == (n * (n - 1)) / 2;
*/
int foo023(int n) {
  int i, sum = 0;

/*@
    loop invariant 0 <= i <= n;
    loop invariant sum == (i * (i - 1)) / 2;
    loop assigns sum, i;
*/
    for (i = 0; i < n; ++i){
        sum = sum + i;
    }

  /*@ assert sum >= 0; */
  return sum; // Return the computed sum
}
