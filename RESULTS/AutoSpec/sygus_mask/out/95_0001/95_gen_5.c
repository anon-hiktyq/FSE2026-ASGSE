void foo(int x) {
  int i = 0;
  int j = 0;
  int y = 0;
  
  /*@
  loop invariant 0 <= i <= x + 1;
  loop invariant j == y * i;
  loop invariant 0 <= j;
  loop invariant y >= 0; 
  loop assigns i;
  loop assigns j;
  */
  while (i <= x) {
    i  = i + 1;
    j  = j + y;
  }

}
