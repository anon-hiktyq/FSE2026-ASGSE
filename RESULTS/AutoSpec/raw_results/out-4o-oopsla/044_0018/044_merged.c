

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
  loop invariant i <= k + 1 || j <= (k + 1) * n;
  loop invariant i <= k + 1 || j <= (k + 1) * n;
  loop invariant i <= k + 1 || i <= k + 1;
  loop invariant i <= k + 1 || 0 < n;
  loop invariant flag == 1 ==> n == 1;
  loop invariant flag == 1 ==> (j == i && n == 1);
  loop invariant \separated(&i, &j, &n, &flag, &k);
  loop invariant \forall integer z; 0 <= z <= i ==> j >= z * n;
  loop invariant \forall integer p; 0 <= p <= i ==> (p <= k + 1 && j >= 0);
  loop invariant \exists integer q; 0 <= q <= k && j == q * n;
  loop invariant 0 <= n;
  loop invariant 0 <= j || j <= (k + 1) * n;
  loop invariant 0 <= j || i <= k + 1;
  loop invariant 0 <= j || i <= k + 1;
  loop invariant 0 <= j || 0 <= i;
  loop invariant 0 <= j || 0 <= i;
  loop invariant 0 <= j || 0 < n;
  loop invariant 0 <= i || j <= (k + 1) * n;
  loop invariant 0 <= i || j <= (k + 1) * n;
  loop invariant 0 <= i || i <= k + 1;
  loop invariant 0 <= i || i <= k + 1;
  loop invariant 0 <= i || i <= k + 1;
  loop invariant 0 <= i || i <= k + 1;
  loop invariant 0 <= i || 0 <= i;
  loop invariant 0 <= i || 0 < n;
  loop invariant 0 <= i || 0 < n;
  loop invariant 0 < n;
  loop invariant 0 < n || j <= (k + 1) * n;
  loop invariant 0 < n || i <= k + 1;
  loop invariant (n == 1 || n == 2) && n == (flag == 1 ? 1 : 2);
  loop invariant ((flag == 1 && n == 1) ==> j == i);
  loop invariant ((flag != 1 && n == 2) ==> j == 2 * i);
  loop invariant n == 1 || n == 2;
  loop invariant n == (flag == 1 ? 1 : 2);
  loop invariant j == i * n;
  loop invariant j <= i * n;
  loop invariant j <= i * n || j <= (k + 1) * n;
  loop invariant j % n == 0;
  loop invariant i <= k + 1 || j <= i * n;
  loop invariant i <= j;
  loop invariant i <= j / n;
  loop invariant i <= j / n || j <= i * n;
  loop invariant i <= j / n || j <= (k + 1) * n;
  loop invariant i <= j / n || i <= k + 1;
  loop invariant flag == 1 || flag != 1;
  loop invariant flag == 1 ==> j == i;
  loop invariant flag == 1 ==> (n == 1 && j == i);
  loop invariant flag == 0 ==> n == 2;
  loop invariant flag != 1 ==> n == 2;
  loop invariant flag != 1 ==> j == 2 * i;
  loop invariant flag != 1 ==> (n == 2 && j == 2 * i);
  loop invariant \separated(&i, &j, &k, &flag, &n);
  loop invariant 1 <= n;
  loop invariant 1 <= n || j <= i * n;
  loop invariant 1 <= n || j <= (k + 1) * n;
  loop invariant 1 <= n || i <= k + 1;
  loop invariant 1 <= n || i <= j / n;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant (n == 1 || n == 2) && (flag == 1 ==> n == 1) && (flag != 1 ==> n == 2);
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
  loop invariant (flag == 0) ==> j == 2 * i;
  loop invariant (flag == 0) ==> (n == 2);
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
