
int unknown();


/*@ requires m > 0;*/
void foo014(int m) {
  int a = 0;
  
  int j = 1;
  /*@
  loop invariant -m <= a <= m;
  loop invariant 1 <= j <= m + 1;
  loop invariant \abs(a) <= j - 1;
  loop invariant \forall integer k; 1 <= k < j ==> -m <= a <= m;
  loop invariant a + j >= 1 && a - j <= 0;
  loop invariant \exists integer k; -m <= k <= m && k == a;
  loop invariant j >= 1 && j <= m + 1;
  loop invariant j > 0 && j <= m + 1;
  loop invariant j <= m + 1;
  loop invariant j - 1 <= m;
  loop invariant a >= -m && a <= m;
  loop invariant a >= -m && a <= j - 1;
  loop invariant a >= -j + 1 && a <= j - 1;
  loop invariant a == 0 ==> \forall integer k; 1 <= k < j ==> a == 0;
  loop invariant a <= m;
  loop invariant a <= m && a >= -m;
  loop invariant a <= j - 1;
  loop invariant a - j <= 0;
  loop invariant a - j <= -1;
  loop invariant a - j < 0;
  loop invariant a + j >= 1 && a - j <= 0;
  loop invariant \forall integer k; 1 <= k < j ==> a >= -m && a <= m;
  loop invariant \forall integer k; 1 <= k < j ==> -m <= a <= m;
  loop invariant \forall integer k; 1 <= k < j ==> -m <= a && a <= m;
  loop invariant \exists integer k; -m <= k <= m && k == a;
  loop invariant \abs(a) <= j - 1;
  loop invariant 1 <= j;
  loop invariant 1 <= j && j <= m + 1;
  loop invariant 1 <= a + j;
  loop invariant 0 <= j;
  loop invariant 0 < j;
  loop invariant 0 < j && j <= m + 1;
  loop invariant -m <= a;
  loop invariant -m <= a && a <= m;
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
