int unknown();

/*@ requires x != y;*/
void foo043(int x, int y) {
  int i=0;
  int t=y;
   
  

  /*@
  loop invariant y == t + i * x;
  loop invariant x > 0 ==> y >= t;
  loop invariant x > 0 ==> y == t + i * x;
  loop invariant x <= 0 ==> y == t;
  loop invariant x < 0 ==> y <= t + i * x;
  loop invariant x != y;
  loop invariant x != 0;
  loop invariant x != 0 ==> \exists integer k; k == i && y == t + k * x;
  loop invariant t + i * x <= y;
  loop invariant \forall integer k; 0 <= k <= i ==> y >= t;
  loop invariant \forall integer k; 0 <= k <= i ==> y >= t + k * x;
  loop invariant \forall integer k; 0 <= k < i ==> y - t >= k * x;
  loop invariant 0 <= i;
  loop invariant x > 0 ==> y >= t + i * x;
  loop invariant t <= y;
  loop invariant \forall integer k; k <= i ==> y >= t;
  loop assigns y;
  loop assigns i;
  */
  while (unknown()){
    if (x > 0)   
      y = y + x;
  }
   
  // @ assert y >= t;*/
 
}

