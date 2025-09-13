void foo(int x) {
  int i = 0;
  int j = 0;
  int y = 0;
  
  /*@
  loop invariant y == 0 || y != 1;
  loop invariant y == 0 || j % y == 0;
  loop invariant y == 0 || i == j + 1;
  loop invariant j == y * (i - 1);
  loop invariant j == (i - 1) * y;
  loop invariant i <= x + 1;
  loop invariant 0 <= y;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop assigns j;
  loop assigns i;
  */
  while (i <= x) {
    i  = i + 1;
    j  = j + y;
  }
  // post-condition
  if (i != j) {
    // @ assert y != 1;
  }
}
