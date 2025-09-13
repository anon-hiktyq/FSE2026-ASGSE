
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
  loop invariant x + y == k;
  loop invariant (j == i) ==> (x == \old(x) + 1) && (y == \old(y) - 1);
  loop invariant (j != i) ==> (x == \old(x) - (j - (j>i?1:0))) && (y == \old(y) + (j - (j>i?1:0)));
  loop invariant (j > i) ==> (x == \old(x) - i - 1) && (y == \old(y) + i + 1);
  loop invariant (j <= i) ==> (x == \old(x) - j) && (y == \old(y) + j);
  loop invariant (m == j - 1 || m == 0);
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