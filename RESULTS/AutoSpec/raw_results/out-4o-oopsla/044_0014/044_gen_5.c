

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
  loop invariant 0 <= j <= (k + 1) * n;
  loop invariant j == i * n;
  loop invariant i == 0 || j >= n;
  loop invariant (flag == 1) ==> (j == i);
  loop invariant (flag != 1) ==> (j == 2 * i);
  loop invariant n == (flag == 1 ? 1 : 2);
  loop invariant \forall integer x; 0 <= x < i ==> j >= (x + 1) * n;
  loop invariant n == (flag == 1 ? 1 : 2);
  loop invariant k >= 0 ==> j == i * n;
  loop invariant k >= 0 ==> j <= n * (k + 1);
  loop invariant k >= 0 ==> j <= (k + 1) * n;
  loop invariant k >= -1 ==> j <= (k + 2) * n;
  loop invariant k < 0 ==> j == 0;
  loop invariant k < 0 ==> i == 0 && j == 0;
  loop invariant j == i * n;
  loop invariant j == (i * (flag == 1 ? 1 : 2));
  loop invariant j == (flag == 1 ? i : 2 * i);
  loop invariant j % n == 0;
  loop invariant i * n <= j;
  loop invariant i * n <= j || i <= k + 1;
  loop invariant flag == 1 ==> n == 1 && j == i;
  loop invariant flag == 1 ==> j == i;
  loop invariant flag != 1 ==> n == 2 && j == 2 * i;
  loop invariant flag != 1 ==> j == 2 * i;
  loop invariant \forall integer x; 0 <= x <= i ==> j >= x * n;
  loop invariant 0 <= j;
  loop invariant 0 <= j || i <= k + 1;
  loop invariant 0 <= j || i * n <= j;
  loop invariant 0 <= i;
  loop invariant 0 <= i && 0 <= j;
  loop invariant 0 < n;
  loop invariant (flag == 1) ==> j == i;
  loop invariant (flag == 1) ==> (n == 1);
  loop invariant (flag == 1) ==> (n == 1 && j == i);
  loop invariant (flag == 1) ==> (j == i);
  loop invariant (flag != 1) ==> j == 2 * i;
  loop invariant (flag != 1) ==> j / 2 == i;
  loop invariant (flag != 1) ==> (n == 2);
  loop invariant (flag != 1) ==> (n == 2 && j == 2 * i);
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
