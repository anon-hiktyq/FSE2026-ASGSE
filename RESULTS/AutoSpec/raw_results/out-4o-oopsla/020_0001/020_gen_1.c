
int unknown();

/*@
requires (x + y) == k;
requires n > 0;
*/
void foo020(int x, int y, int k, int j, int i, int n) {
 
  int m = 0;
  j = 0;
  /*@
  loop invariant 0 <= j <= n;
  loop invariant (x + y) == k;
  loop invariant m == -1 || (0 <= m && m < n);
  loop invariant m == -1 || m == j - 1;
  loop assigns j, x, y, m;
  */
  while (j < n) {
    if (j == i) {
      x++;
      y--;
    } else {
      y++;
      x--;
    }
    if (unknown()){
       m = j;
    }
    j++;
  }
  // @ assert (x + y) == k;
  
  //@ assert(n > 0) ==> (0 <= m && m < n);
  

}