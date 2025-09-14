
/*@
    requires (x + y) == k;
    requires n > 0;
*/
void foo61(int x, int y, int k, int j, int i, int n) {
 
  int m = 0;
  j = 0;
  
  /*@
      loop invariant (0 < \at(n,Pre)) ==> (x + y == k);
      loop invariant (0 < \at(n,Pre)) ==> (0 <= j <= n);
      loop invariant (0 < \at(n,Pre)) ==> (m == 0 || (0 <= m < j));
      loop invariant (0 < \at(n,Pre)) ==> (((m == 0)&&(n == \at(n,Pre))&&(i == \at(i,Pre))&&(j == 0)&&(k == \at(k,Pre))&&(y == \at(y,Pre))&&(x == \at(x,Pre))) || ((m == 0 || (0 <= m < j)) && (x + y == k)));
      loop invariant (!(0 < \at(n,Pre))) ==> ((m == 0)&&(n == \at(n,Pre))&&(i == \at(i,Pre))&&(j == 0)&&(k == \at(k,Pre))&&(y == \at(y,Pre))&&(x == \at(x,Pre)));
      loop invariant n == \at(n,Pre);
      loop invariant i == \at(i,Pre);
      loop invariant k == \at(k,Pre);
      loop assigns j, x, y, m;
      loop variant n - j;
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
            
  /*@ assert (x + y) == k; */
  
  /*@ assert(n > 0) ==> (0 <= m && m < n); */
}
