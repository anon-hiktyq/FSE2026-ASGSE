


void foo011() {
  int j = 0;
  int i = 0;
  int x = 100;
   
 
  /*@
  loop invariant j == 2*i;
  loop invariant j == 2 * i;
  loop invariant i <= x;
  loop invariant 0 <= i;
  loop assigns j;
  loop assigns i;
  */
  for (i = 0; i < x ; i++){
    j = j + 2;
  }

  // @ assert j == 2*x;
}
