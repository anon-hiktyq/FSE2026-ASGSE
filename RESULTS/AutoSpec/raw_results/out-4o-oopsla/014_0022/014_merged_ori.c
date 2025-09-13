
int unknown();


/*@ requires m > 0;*/
void foo014(int m) {
  int a = 0;
  
  int j = 1;
  /*@
  loop invariant j >= 1 && j <= m + 1;
  loop invariant j - 1 <= m - a;
  loop invariant j - 1 <= a + m;
  loop invariant j - 1 - m <= a && a <= m - (j - 1);
  loop invariant a == m - (j - 1) || a == -(j - 1);
  loop invariant a == j - 1 || a == -(j - 1);
  loop invariant a == 0 ==> j % 2 == 1;
  loop invariant a - m <= -(j - 1);
  loop invariant a - j + 1 <= 0;
  loop invariant \sum(0, j - 1, unknown()) - \sum(0, j - 1, !unknown()) == a;
  loop invariant \forall integer k; 1 <= k < j ==> -m <= a <= m;
  loop invariant \forall integer k; 1 <= k < j ==> (k % 2 == 0 ==> a >= -(m - k)) && (k % 2 == 1 ==> a <= (m - k));
  loop invariant \forall integer k; 1 <= k < j ==> (-k + 1 <= a <= k - 1);
  loop invariant \exists integer k; 1 <= k <= j && a == -m + k - 1 || a == m - k + 1;
  loop invariant \exists integer k; 1 <= k < j && (a == m - k || a == -(k - 1));
  loop invariant \abs(a) <= m;
  loop invariant \abs(a) <= j - 1;
  loop invariant \abs(a) + j - 1 <= m;
  loop invariant 0 <= j;
  loop invariant 0 <= a + j - 1;
  loop invariant -m <= a && a <= m;
  loop invariant -j <= a && a <= j - 1;;
  loop invariant j <= m + 1;
  loop invariant a >= -m && a <= m;
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
