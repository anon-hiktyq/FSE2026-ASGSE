

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
  loop invariant n == (flag == 1 ? 1 : 2);;
  loop invariant k >= 0 ==> j <= (k + 1) * n;
  loop invariant k < 0 ==> i == 0 && j == 0;
  loop invariant j == i * n;;
  loop invariant j == (i * (flag == 1 ? 1 : 2));
  loop invariant j <= n * (k + 1);
  loop invariant j <= (k + 1) * n;;
  loop invariant i == \floor_div(j, n);;
  loop invariant i <= k + 1;;
  loop invariant i <= k + 1;
  loop invariant \forall integer x; 0 <= x <= i ==> j == x * n;
  loop invariant \forall integer m; 0 <= m < i ==> j == m * n;
  loop invariant 0 <= j;
  loop invariant 0 < n;
  loop invariant (flag == 1) ==> n == 1;;
  loop invariant (flag == 1) ==> (n == 1 && j == i);
  loop invariant (flag == 1) ==> (j == i);
  loop invariant (flag != 1) ==> n == 2;;
  loop invariant (flag != 1) ==> (n == 2 && j == 2 * i);
  loop invariant (flag != 1) ==> (j == 2 * i);
  loop invariant n == (flag == 1 ? 1 : 2);
  loop invariant j == i * n;
  loop invariant 0 <= i;
  loop invariant (flag == 1) ==> (n == 1);
  loop invariant (flag != 1) ==> (n == 2);
  loop assigns j;
  loop assigns i;
  */
  while ( i <= k) {
    i++;
    j = j + n;
  }
  // @ assert (flag == 1) ==> (j == i);*/
    
	
}
