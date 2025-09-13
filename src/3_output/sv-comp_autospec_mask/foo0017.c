
void foo0017(int tmp, int A[2048], int B[2048]) {
  int i = 0;
  
  /* >>> LOOP INVARIANT TO FILL <<< */
  
  /*@
    loop invariant  ((i == 0)&&(B == \at(B,Pre))&&(A == \at(A,Pre))&&(tmp == \at(tmp,Pre))) || (tmp == A[i-1]) ;
    loop invariant  0 <= i <= 2048 ;
    loop invariant B == \at(B,Pre);
    loop invariant A == \at(A,Pre);
    loop invariant \forall integer j; 0 <= j < i ==> B[j] == A[j];
  */
  for (i = 0; i < 2048; i++) {
    tmp = A[i];
    B[i] = tmp;
  }
  
  /*@assert A[1024] == B[1024];*/
}
