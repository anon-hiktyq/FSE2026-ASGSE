
int unknown();


/*@ requires m > 0;*/
void foo014(int m) {
  int a = 0;
  
  int j = 1;
  /*@
  loop invariant -m <= a && a <= m;
  loop invariant -j <= a && a <= j - 1;
  loop invariant abs(a) <= m;
  loop invariant abs(a) <= j - 1;
  loop invariant 1 <= j <= m + 1;
  loop invariant (j - 1) - abs(a) >= 0;
  loop invariant a + j - 1 >= 0 && -a + j - 1 >= 0;
  loop invariant j >= 1 && j <= m + 1;
  loop invariant j <= m + 1;
  loop invariant a >= -m && a <= m;
  loop invariant a >= -j + 1 && a <= j - 1;
  loop invariant a <= m;
  loop invariant a <= j - 1;
  loop invariant a <= j - 1 || \abs(a) <= j - 1;
  loop invariant a <= j - 1 || 1 <= a + j;
  loop invariant a <= j - 1 || 0 <= j;
  loop invariant a <= j - 1 || 0 <= (j - 1) - \abs(a);
  loop invariant \abs(a) <= m;
  loop invariant \abs(a) <= m || 0 <= (j - 1) - \abs(a);
  loop invariant \abs(a) <= j - 1;
  loop invariant \abs(a) <= j - 1 || \abs(a) <= m;
  loop invariant \abs(a) <= j - 1 || 1 <= a + j;
  loop invariant \abs(a) <= j - 1 || 0 <= j;
  loop invariant \abs(a) <= j - 1 || 0 <= (j - 1) - \abs(a);
  loop invariant 1 <= j;
  loop invariant 1 <= a + j;
  loop invariant 1 <= a + j || \abs(a) <= m;
  loop invariant 1 <= a + j || 0 <= (j - 1) - \abs(a);
  loop invariant 1 <= -a + j;
  loop invariant 1 <= -a + j || \abs(a) <= m;
  loop invariant 1 <= -a + j || \abs(a) <= j - 1;
  loop invariant 1 <= -a + j || 1 <= a + j;
  loop invariant 1 <= -a + j || 0 <= (j - 1) - \abs(a);
  loop invariant 0 <= j;
  loop invariant 0 <= j || 1 <= a + j;
  loop invariant 0 <= a + j - 1;
  loop invariant 0 <= a + j - 1 && 0 <= -a + j - 1;
  loop invariant 0 <= -a + j - 1;
  loop invariant 0 <= (j - 1) - \abs(a);
  loop invariant 0 <= (j - 1) - \abs(a) || 1 <= a + j;
  loop invariant 0 <= (j - 1) - \abs(a) || 0 <= j;
  loop invariant 0 < j;
  loop invariant -m <= a;
  loop invariant -m <= a && a <= m;
  loop invariant -j <= a;
  loop invariant -j <= a && a <= j - 1;
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
