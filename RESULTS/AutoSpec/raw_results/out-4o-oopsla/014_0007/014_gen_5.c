
int unknown();


/*@ requires m > 0;*/
void foo014(int m) {
  int a = 0;
  
  int j = 1;
  /*@
  loop invariant \abs(a) <= j - 1;
  loop invariant \forall integer k; 1 <= k <= j ==> -k <= a <= k - 1;
  loop invariant a % 2 == (j - 1) % 2;
  loop invariant j >= 1;
  loop invariant m >= j - 1;
  loop assigns a;
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
