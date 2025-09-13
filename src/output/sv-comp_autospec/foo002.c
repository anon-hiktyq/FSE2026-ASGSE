
void foo002(int A[2048]) {
  int i = 0;

  
  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant 0 <= i <= 1024;
            loop invariant \forall integer j; 0 <= j < i ==> A[j] == j;
            loop invariant A == \at(A,Pre);
            loop assigns A[0..1023], i;
            */
            for (i = 0; i < 1024; i++) {
    A[i] = i;
  }
            

  /*@ assert A[1023] == 1023; */
}
