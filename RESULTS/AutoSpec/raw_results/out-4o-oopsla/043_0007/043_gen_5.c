int unknown();

/*@ requires x != y;*/
void foo043(int x, int y) {
  int i=0;
  int t=y;
   
  

  /*@
  loop invariant x > 0 ==> y == t + i * x;
  loop invariant i >= 0;
  loop invariant t <= y;
  loop invariant y >= t + i * x;
  loop invariant \forall integer k; 0 <= k <= i ==> y >= t + k * x;
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

