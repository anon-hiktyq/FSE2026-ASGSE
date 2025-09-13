
/*@
requires n > 0;
requires k > n;
*/
void foo015(int n, int k) {

  int j = 0;

  while( j < n ) {
    j++;
    k--;
  } 
  /*@ assert k>=0; */
}