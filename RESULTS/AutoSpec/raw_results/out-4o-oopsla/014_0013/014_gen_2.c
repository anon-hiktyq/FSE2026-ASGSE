
int unknown();


/*@ requires m > 0;*/
void foo014(int m) {
  int a = 0;
  
  int j = 1;
  /*@
  loop invariant -m <= a && a <= m;
  loop invariant -j <= a && a <= j - 1;
  loop invariant j >= 1;
  loop invariant j <= m + 1;
  loop invariant \abs(a) <= j - 1;
  loop invariant \abs(a) <= m;
  loop invariant 0 <= a + j - 1;
  loop invariant 0 <= -a + j - 1;
  loop assigns a, j;
  loop invariant j >= 1 && j <= m + 1;
  loop invariant j <= m + 1;
  loop invariant a >= -m && a <= m;
  loop invariant a >= -j + 1 && a <= j - 1;
  loop invariant a <= m;
  loop invariant a <= j - 1;
  loop invariant \abs(a) <= m;
  loop invariant \abs(a) <= j - 1;
  loop invariant 1 <= j;
  loop invariant 0 <= a + j - 1;
  loop invariant 0 <= -a + j - 1;
  loop invariant -m <= a;
  loop invariant -j <= a;
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
