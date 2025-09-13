int unknown();


/*@
requires n > 0;
*/
void foo07(int n) {

  int i, a, b;
  i = 0; a = 0; b = 0;
  
  /*@
  loop invariant 0 <= i <= n;
  loop invariant a + b == 3 * i;
  loop assigns i, a, b;
  */
  while( i < n ) {
    if(unknown()) {
      a = a + 1;
      b = b + 2;
    } else {
      a = a + 2;
      b = b + 1;
    }
    i = i + 1;
  }
  // @ assert a + b == 3*n ;
}
