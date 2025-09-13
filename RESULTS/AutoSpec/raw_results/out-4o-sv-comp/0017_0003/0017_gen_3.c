

void foo0017(int tmp, int A[2048], int B[2048]) {
  int i = 0;
  
  /*@
  loop invariant 0 <= i <= 2048;
  loop invariant \forall integer k; 0 <= k < i ==> A[k] == B[k];
  loop assigns i;
  loop assigns tmp;
  loop assigns B[0..2047];
  */
  for (i = 0; i < 2048; i++) {
    tmp = A[i];
    B[i] = tmp;
  }

  /*@assert A[1024] == B[1024];*/
}
