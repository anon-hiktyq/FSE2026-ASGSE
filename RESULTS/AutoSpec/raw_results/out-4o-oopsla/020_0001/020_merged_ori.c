
int unknown();

/*@
requires (x + y) == k;
requires n > 0;
*/
void foo020(int x, int y, int k, int j, int i, int n) {
 
  int m = 0;
  j = 0;
  /*@
  loop invariant x + y == k;
  loop invariant m == 0 || (0 <= m < j);
  loop invariant m == -1 || m == j - 1;
  loop invariant m == -1 || (0 <= m && m < n);
  loop invariant j >= n ==> (0 <= m < n);
  loop invariant j == i ==> (x + y) == k;
  loop invariant j <= n;
  loop invariant j < n ==> (m == 0 || 0 <= m < n);
  loop invariant j < n ==> (0 <= m < n);
  loop invariant j != i ==> (x + y) == k;
  loop invariant 0 <= m;
  loop invariant 0 <= j;
  loop invariant 0 < n;
  loop invariant (x + y) == k;
  loop invariant (m == j - 1 || m == 0);
  loop invariant (m == 0 || (0 <= m && m <= j && unknown()));
  loop invariant (j > i) ==> (x == \old(x) - i - 1) && (y == \old(y) + i + 1);
  loop invariant (j > i) ==> ((x + y) == k - 2 * (j - i));
  loop invariant (j > 0) ==> (0 <= m < n);
  loop invariant (j == i) ==> (x == \old(x) + 1) && (y == \old(y) - 1);
  loop invariant (j == i) ==> (x + y == k);
  loop invariant (j <= i) ==> (x == \old(x) - j) && (y == \old(y) + j);
  loop invariant (j <= i) ==> (x + y == k);
  loop invariant (j != i) ==> (x == \old(x) - (j - (j>i?1:0))) && (y == \old(y) + (j - (j>i?1:0)));
  loop invariant (j != i) ==> (x + y == k);
  loop invariant (0 <= m && m < j) || (m == 0);
  loop assigns y;
  loop assigns x;
  loop assigns m;
  loop assigns j;
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