
/*@
requires n >= 0;
*/
void foo62(int n) {
  int i, sum = 0;
 
  for (i = 0; i < n; ++i){
    sum = sum + i;
  }

  /*@ assert sum >= 0; */
}