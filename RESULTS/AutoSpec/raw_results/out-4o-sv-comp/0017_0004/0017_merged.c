

void foo0017(int tmp, int A[2048], int B[2048]) {
  int i = 0;
  
  /*@
  loop invariant i <= 2048;
  loop invariant 0 <= i;
  loop assigns tmp;
  loop assigns i;
  loop assigns B[0..2047];
  */
  for (i = 0; i < 2048; i++) {
    tmp = A[i];
    B[i] = tmp;
  }

}
