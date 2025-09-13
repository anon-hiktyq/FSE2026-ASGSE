
void foo0017(int tmp, int A[2048], int B[2048]) {
  int i = 0;
  
  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              loop invariant 0 <= i <= 2048;
              loop invariant B == \at(B,Pre);
              loop invariant A == \at(A,Pre);
              loop invariant \forall integer j; i <= j < 2048 ==> B[j] == \at(B,Pre)[j];  // B remains unchanged for unprocessed indices
              loop assigns i, B[0..2047], tmp;
            */
            for (i = 0; i < 2048; i++) {
    tmp = A[i];
    B[i] = tmp;
  }
            

  /*@assert A[1024] == B[1024];*/
}
