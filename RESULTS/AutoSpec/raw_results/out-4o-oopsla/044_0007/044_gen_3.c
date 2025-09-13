

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
  loop invariant 0 <= i <= k + 1; 
  loop invariant i == j / n;
  loop invariant j == n * i;
  loop invariant n == (flag == 1 ? 1 : 2);
  loop invariant \forall integer m; 0 <= m < i ==> j == n * m;
  loop invariant flag == 1 ? j == i : j == 2 * i;
  loop invariant 0 <= j;
  loop invariant n > 0;
  loop invariant n == 1 || n == 2;
  loop invariant n == (flag == 1 ? 1 : 2);
  loop invariant j == n * i;
  loop invariant j == n * i && n == (flag == 1 ? 1 : 2);
  loop invariant j == i * n;
  loop invariant i == j / n;
  loop invariant i == j / n && j % n == 0;
  loop invariant flag == 1 ? j == i : j == 2 * i;
  loop invariant flag == 1 ==> j == i;
  loop invariant flag == 1 ==> j == i * n;
  loop invariant flag == 0 ==> j == 2 * i;
  loop invariant flag != 1 ==> j == 2 * i;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant 0 < n;
  loop invariant (flag == 1) ==> j == i;
  loop invariant (flag == 1) ==> (n == 1);
  loop invariant (flag == 1) ==> (j == i);
  loop invariant (flag == 1) ==> (j == i * n);
  loop invariant (flag == 1 && n == 1) ==> j == i;
  loop invariant (flag != 1) ==> j == 2 * i;
  loop invariant (flag != 1) ==> (n == 2);
  loop invariant (flag != 1 && n == 2) ==> j == 2 * i;
  loop assigns j;
  loop assigns i;
  */
  while ( i <= k) {
    i++;
    j = j + n;
  }
  // @ assert (flag == 1) ==> (j == i);*/
    
	
}
