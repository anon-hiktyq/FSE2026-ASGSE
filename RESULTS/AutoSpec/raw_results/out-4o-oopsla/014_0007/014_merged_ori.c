
int unknown();


/*@ requires m > 0;*/
void foo014(int m) {
  int a = 0;
  
  int j = 1;
  /*@
  loop invariant j > 0 && j <= m + 1;
  loop invariant j == abs(a) + 1 || j == abs(a) + 2;
  loop invariant j - 1 <= m;
  loop invariant j - 1 <= a + m;
  loop invariant a <= m && a >= -m;
  loop invariant a - m <= -(j - 1);
  loop invariant a - j <= -1;
  loop invariant a + j >= 1 && a - j <= 0;
  loop invariant a + j <= m + 1;
  loop invariant a % 2 == m % 2;
  loop invariant a % 2 == j % 2;
  loop invariant a % 2 == (j - 1) % 2;
  loop invariant a % 2 == (j % 2) - 1;
  loop invariant a % 2 == (j % 2 == 1 ? 1 : 0);
  loop invariant \forall integer k; 1 <= k <= j ==> -k <= a <= k;
  loop invariant \forall integer k; 1 <= k <= j ==> -k <= a <= k - 1;
  loop invariant \forall integer k; 1 <= k <= j ==> -k + 1 <= a <= k - 1;
  loop invariant \forall integer k; 1 <= k < j ==> a >= -m && a <= m;
  loop invariant \forall integer k; 1 <= k < j ==> \abs(a) <= k - 1;
  loop invariant \forall integer k; 1 <= k < j ==> -m <= a <= m;
  loop invariant \forall integer k; 1 <= k < j ==> -k + 1 <= a <= k - 1;
  loop invariant \exists integer k; 1 <= k <= m && a >= -k + 1 && a <= k - 1;;
  loop invariant \exists integer k; -m <= k <= m && k == a;
  loop invariant \abs(a) <= j - 1;
  loop invariant 1 <= j && j <= m + 1;
  loop invariant 1 <= a + j;
  loop invariant 0 <= j;
  loop invariant 0 < j;
  loop invariant -m <= a && a <= m;
  loop invariant -m - 1 <= a - j;
  loop invariant j <= m + 1;
  loop invariant a >= -m && a <= m;
  loop invariant a >= -j + 1 && a <= j - 1;
  loop invariant a <= m;
  loop invariant a <= j - 1;
  loop invariant 1 <= j;
  loop invariant -m <= a;
  loop invariant -j + 1 <= a;
  loop assigns j;
  loop assigns a;
  */
  for(j = 1; j <= m ; j++){
    if(unknown()) 
       a++;
    else
       a--; 
  }
  // @ assert a>= -m && a <= m;*/
}
