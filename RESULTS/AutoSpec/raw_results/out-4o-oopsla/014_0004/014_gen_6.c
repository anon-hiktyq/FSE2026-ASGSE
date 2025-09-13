
int unknown();


/*@ requires m > 0;*/
void foo014(int m) {
  int a = 0;
  
  int j = 1;
  /*@
  loop invariant -m <= a <= m;
  loop invariant 1 <= j <= m + 1;
  loop invariant -j <= a <= j;
  loop invariant j == m + 1 ==> a >= -m && a <= m;
  loop invariant \abs(a) <= j - 1;
  loop invariant j == m + 1 ==> a >= -m && a <= m;
  loop invariant j <= m+1;
  loop invariant j <= m + 1;
  loop invariant j <= m + 1 || a <= j - 1;
  loop invariant j <= m + 1 || \abs(a) <= j - 1;
  loop invariant j <= m + 1 || 0 <= j;
  loop invariant a >= -m && a <= m;
  loop invariant a >= -j + 1 && a <= j - 1;
  loop invariant a >= -j && a <= j;
  loop invariant a <= m;
  loop invariant a <= m || j <= m + 1;
  loop invariant a <= m || a <= j - 1;
  loop invariant a <= m || \abs(a) <= j - 1;
  loop invariant a <= m || 0 <= j;
  loop invariant a <= j;
  loop invariant a <= j-1;
  loop invariant a <= j - 1;
  loop invariant a < j;
  loop invariant a - j <= 0;
  loop invariant a + j <= m + j;
  loop invariant a + j <= 2*j;
  loop invariant a + j <= 2*j - 1;
  loop invariant a + j <= 2 * j;
  loop invariant a + j <= 2 * j - 1;
  loop invariant a + j <= 2 * j - 1 || j <= m + 1;
  loop invariant a + j <= 2 * j - 1 || a <= m;
  loop invariant a + j <= 2 * j - 1 || a <= j - 1;
  loop invariant a + j <= 2 * j - 1 || \abs(a) <= j - 1;
  loop invariant a + j <= 2 * j - 1 || \abs(a + j) <= 2 * j;
  loop invariant a + j <= 2 * j - 1 || 0 <= j;
  loop invariant \abs(a) <= j - 1;
  loop invariant \abs(a) <= j - 1 || a <= j - 1;
  loop invariant \abs(a + j) <= 2 * j || j <= m + 1;
  loop invariant \abs(a + j) <= 2 * j || a <= m;
  loop invariant \abs(a + j) <= 2 * j || a <= j - 1;
  loop invariant \abs(a + j) <= 2 * j || \abs(a) <= j - 1;
  loop invariant \abs(a + j) <= 2 * j || 0 <= j;
  loop invariant 1 <= j;
  loop invariant 0 <= j;
  loop invariant 0 <= j || a <= j - 1;
  loop invariant 0 <= j || \abs(a) <= j - 1;
  loop invariant 0 <= a + j;
  loop invariant 0 < j;
  loop invariant -m <= a;
  loop invariant -j+1 <= a;
  loop invariant -j <= a;
  loop invariant -j < a;
  loop invariant -j + 1 <= a;
  loop invariant -(j - 1) <= a;
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
