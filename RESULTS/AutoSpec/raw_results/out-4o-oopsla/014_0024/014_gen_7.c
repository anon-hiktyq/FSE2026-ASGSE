
int unknown();


/*@ requires m > 0;*/
void foo014(int m) {
  int a = 0;
  
  int j = 1;
  /*@
  loop invariant \abs(a) <= j - 1;
  loop invariant \abs(a) <= m;
  loop invariant -m <= a <= m;
  loop invariant j - 1 <= m;
  loop invariant j >= 1;
  loop invariant \forall integer k; 1 <= k <= j ==> -m <= a <= m;
  loop invariant \forall integer k; 0 <= k <= j-1 ==> \abs(a) <= m;
  loop invariant \exists integer k; 0 <= k <= j-1 ==> \abs(a) <= m;
  loop invariant j - 1 <= a + m;
  loop invariant \abs(a) <= m && a >= -m;
  loop invariant j >= 1 && j <= m + 1;
  loop invariant j <= m + 1;
  loop invariant j <= m + 1 || a <= m;
  loop invariant j <= m + 1 || a <= j - 1;
  loop invariant j <= m + 1 || 1 <= j + a;
  loop invariant j <= m + 1 || 0 <= a + m;
  loop invariant j - a <= m + 1 || j <= m + 1;
  loop invariant j - a <= m + 1 || a <= m;
  loop invariant j - a <= m + 1 || a <= j - 1;
  loop invariant j - a <= m + 1 || 1 <= j + a;
  loop invariant j - a <= m + 1 || 0 <= a + m;
  loop invariant j - 1 <= a + m || j <= m + 1;
  loop invariant j - 1 <= a + m || a <= m;
  loop invariant j - 1 <= a + m || a <= j - 1;
  loop invariant j - 1 <= a + m || 1 <= j + a;
  loop invariant j - 1 <= a + m || 0 <= a + m;
  loop invariant a >= 0 || a >= -m;
  loop invariant a >= -m && a <= m;
  loop invariant a <= m;
  loop invariant a <= m || a <= j - 1;
  loop invariant a <= m || 0 <= a + m;
  loop invariant a <= j - 1;
  loop invariant a - j + 1 <= 0;
  loop invariant \forall integer k; 1 <= k < j ==> \abs(a) <= m;
  loop invariant \forall integer k; 1 <= k < j ==> -m <= a <= m;
  loop invariant \abs(a) <= m;
  loop invariant \abs(a) <= j - 1;
  loop invariant \abs(a) <= j - 1 || j <= m + 1;
  loop invariant \abs(a) <= j - 1 || j - a <= m + 1;
  loop invariant \abs(a) <= j - 1 || j - 1 <= a + m;
  loop invariant \abs(a) <= j - 1 || a <= m;
  loop invariant \abs(a) <= j - 1 || a <= j - 1;
  loop invariant \abs(a) <= j - 1 || 1 <= j + a;
  loop invariant \abs(a) <= j - 1 || 0 <= a + m;
  loop invariant \abs(a) <= j - 1 || 0 <= (j - 1 - a);
  loop invariant 1 <= j;
  loop invariant 1 <= j + a;
  loop invariant 1 <= j + a || a <= m;
  loop invariant 1 <= j + a || a <= j - 1;
  loop invariant 1 <= j + a || 0 <= a + m;
  loop invariant 0 <= j;
  loop invariant 0 <= a + m;
  loop invariant 0 <= a + m || a <= j - 1;
  loop invariant 0 <= a + j - 1;
  loop invariant 0 <= (j - 1 - a);
  loop invariant 0 <= (j - 1 - a) || j <= m + 1;
  loop invariant 0 <= (j - 1 - a) || j - a <= m + 1;
  loop invariant 0 <= (j - 1 - a) || j - 1 <= a + m;
  loop invariant 0 <= (j - 1 - a) || a <= m;
  loop invariant 0 <= (j - 1 - a) || a <= j - 1;
  loop invariant 0 <= (j - 1 - a) || 1 <= j + a;
  loop invariant 0 <= (j - 1 - a) || 0 <= a + m;
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
