

void foo044(int k, int flag , int __BLAST_NONDET) {
  int i=0;
  int j=0;
  int n;
 

  if (flag == 1){
     n=1;
  } else {
     n=2;
  }

  i=0;
  
  /*@
  loop invariant i <= k + 1;
  loop invariant n >= 1;
  loop invariant 0 <= j <= (k + 1) * n;
  loop invariant j % n == 0;
  loop invariant j >= i;
  loop invariant j == i * n;
  loop invariant (flag != 1) ==> j % 2 == 0;
  loop invariant (flag == 1) ==> n == 1;
  loop invariant (flag != 1) ==> n == 2;
  loop invariant n == 1 || n == 2;
  loop invariant j == i * n;
  loop invariant i * n == j;
  loop invariant flag == 2 ==> j == 2 * i;
  loop invariant flag == 1 ==> n == 1;
  loop invariant flag == 1 ==> j == i;
  loop invariant flag != 1 ==> n == 2;
  loop invariant flag != 1 ==> j == 2*i;
  loop invariant flag != 1 ==> j == 2 * i;
  loop invariant \forall integer m; 0 <= m <= i ==> j >= m;
  loop invariant \forall integer m; 0 <= m <= i ==> j % n == 0;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant (n == 1 || n == 2);
  loop invariant (flag == 2) ==> j == 2 * i;
  loop invariant (flag == 1) ==> (j == i);
  loop invariant (flag != 1) ==> (j == 2 * i);
  loop assigns j;
  loop assigns i;
  */
  while ( i <= k) {
    i++;
    j = j + n;
  }
  // @ assert (flag == 1) ==> (j == i);*/
    
	
}
