
/*@
requires n > 0;
*/
void foo035(int n) {
  int x= 0;
  
  /*@
  loop invariant 0 <= x <= n;
  loop invariant x <= n;
  loop invariant n > 0;
  loop assigns x;
  */
  while(x<n) {
    x++;
  } 
  // @ assert (n > 0) ==> (x == n);
 
}
