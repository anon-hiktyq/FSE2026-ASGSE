
/*@
requires n > 0;
*/
void foo035(int n) {
  int x= 0;
  
  /*@
  loop invariant x <= n;
  loop invariant \forall integer k; 0 <= k < x ==> k < n;
  loop invariant 0 <= x;
  loop invariant 0 < n;
  loop assigns x;
  */
  while(x<n) {
    x++;
  } 
  //@ assert (n > 0) ==> (x == n);
 
}
