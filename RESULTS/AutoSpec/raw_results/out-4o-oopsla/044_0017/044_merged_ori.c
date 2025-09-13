

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
  loop invariant j <= i * n;
  loop invariant j <= i * n || j <= (k + 1) * n;
  loop invariant j <= (k + 1) * n;
  loop invariant j < i * n;
  loop invariant j < (k + 1) * n;
  loop invariant j % n == 0;
  loop invariant i <= k + 1;
  loop invariant i <= k + 1 || j <= i * n;
  loop invariant i <= k + 1 || j <= (k + 1) * n;
  loop invariant i <= j / n;
  loop invariant i <= j / n || j <= i * n;
  loop invariant i <= j / n || j <= (k + 1) * n;
  loop invariant i <= j / n || i <= k + 1;
  loop invariant i < k + 1;
  loop invariant i < j / n;
  loop invariant flag == 1 || flag == 0;
  loop invariant flag == 1 ==> j == i;
  loop invariant flag == 1 ==> (n == 1 && j == i);
  loop invariant flag == 0 || flag == 1;
  loop invariant flag == 0 ==> n == 2;
  loop invariant flag != 1 ==> n == 2;
  loop invariant flag != 1 ==> j == 2 * i;
  loop invariant flag != 1 ==> (n == 2 && j == 2 * i);
  loop invariant \separated(&i, &j, &k, &flag, &n);
  loop invariant \forall integer m; 0 <= m < i ==> j == m * n;
  loop invariant \forall integer b; 0 <= b < i ==> j == b * n;
  loop invariant \forall integer a; 0 <= a <= i ==> n == (flag == 1 ? 1 : 2);;
  loop invariant 1 <= n;
  loop invariant 1 <= n || j <= i * n;
  loop invariant 1 <= n || j <= (k + 1) * n;
  loop invariant 1 <= n || i <= k + 1;
  loop invariant 1 <= n || i <= j / n;
  loop invariant 1 < n;
  loop invariant (n == 1 || n == 2) && (flag == 1 ==> n == 1) && (flag != 1 ==> n == 2);
  loop invariant (flag == 1) ==> j == i;;
  loop invariant (flag == 1) ==> (j <= k + 1);
  loop invariant (flag == 0) ==> j == 2 * i;
  loop invariant (flag == 0) ==> (n == 2);
  loop invariant (flag == 0) <==> n == 2;
  loop invariant n == 1 || n == 2;
  loop invariant n == (flag == 1 ? 1 : 2);
  loop invariant j == i * n;
  loop invariant i <= j;
  loop invariant flag == 1 || flag != 1;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant (flag == 1) ==> n == 1;
  loop invariant (flag == 1) ==> j == i;
  loop invariant (flag == 1) ==> (n == 1);
  loop invariant (flag == 1) ==> (n == 1 && j == i);
  loop invariant (flag == 1) ==> (j == i);
  loop invariant (flag == 1) ==> (j == i && n == 1);
  loop invariant (flag == 1) <==> n == 1;
  loop invariant (flag == 1 ==> n == 1) && (flag != 1 ==> n == 2);
  loop invariant (flag == 1 && n == 1) ==> j == i;
  loop invariant (flag == 1 && n == 1) ==> (j == i);
  loop invariant (flag == 0) ==> (j == 2 * i);
  loop invariant (flag != 1) ==> n == 2;
  loop invariant (flag != 1) ==> j == 2 * i;
  loop invariant (flag != 1) ==> (n == 2);
  loop invariant (flag != 1) ==> (n == 2 && j == 2 * i);
  loop invariant (flag != 1) ==> (j == 2*i && n == 2);
  loop invariant (flag != 1) ==> (j == 2 * i);
  loop invariant (flag != 1 && n == 2) ==> j == 2 * i;
  loop invariant (flag != 1 && n == 2) ==> (j == 2 * i);
  loop assigns j;
  loop assigns i;
  */
  while ( i <= k) {
    i++;
    j = j + n;
  }
  // @ assert (flag == 1) ==> (j == i);*/
    
	
}
