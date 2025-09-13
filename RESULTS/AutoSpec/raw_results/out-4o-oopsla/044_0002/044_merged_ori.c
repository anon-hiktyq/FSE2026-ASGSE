

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
  loop invariant n == 1 || n == 2;
  loop invariant j == i * n;;
  loop invariant j <= (k + 1) * n;
  loop invariant i <= k+1;
  loop invariant i <= k + 1;;
  loop invariant i <= k + 1;
  loop invariant i * n == j;
  loop invariant flag == 2 ==> j == 2 * i;
  loop invariant flag == 1 || flag == 0;;
  loop invariant flag == 1 ==> n == 1;
  loop invariant flag == 1 ==> j == i;;
  loop invariant flag != 1 ==> n == 2;
  loop invariant flag != 1 ==> j == 2*i;
  loop invariant flag != 1 ==> j == 2 * i;
  loop invariant \forall integer m; 0 <= m <= i ==> j >= m;
  loop invariant \forall integer m; 0 <= m <= i ==> j % n == 0;
  loop invariant \forall integer m; 0 <= m <= i ==> (flag == 1 ==> j == m);
  loop invariant \forall integer m; 0 <= m < i ==> (flag == 1 ==> j == m + 1);
  loop invariant \forall integer l; 0 <= l < i ==> (flag != 1 ==> j == 2 * l);
  loop invariant \exists integer m; 0 <= m <= i && (flag == 2 && j == 2 * m);
  loop invariant 0 <= j;
  loop invariant 0 <= i;;
  loop invariant (n == 1 || n == 2);
  loop invariant (flag == 2) ==> j == 2 * i;
  loop invariant (flag != 1) ==> (j == 2 * i);;
  loop invariant (flag != 1) ==> (j == 2 * i);
  loop invariant (\forall integer l; 0 <= l < i ==> j == l * n);
  loop invariant j == i * n;
  loop invariant flag == 1 ==> j == i;
  loop invariant 0 <= i;
  loop invariant (flag == 1) ==> (j == i);
  loop assigns j;
  loop assigns i;
  */
  while ( i <= k) {
    i++;
    j = j + n;
  }
  // @ assert (flag == 1) ==> (j == i);*/
    
	
}
