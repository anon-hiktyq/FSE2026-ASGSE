int unknown();

/*@ requires x != y;*/
void foo043(int x, int y) {
  int i=0;
  int t=y;
   
  

  /*@
  loop invariant x != 0;
  loop invariant x > 0 ==> y == t + x * i;
  loop invariant x > 0 ==> y >= t + x * i;
  loop invariant y >= t;
  loop invariant i >= 0;
  loop invariant \forall integer k; 0 <= k < i ==> y >= t + x * k;
  loop invariant y == t || y > t;
  loop invariant x > 0 ==> y >= t + x * i;
  loop invariant t <= y;
  loop assigns y;
  loop assigns x;
  loop assigns i;
  */
  while (unknown()){
    if (x > 0)   
      y = y + x;
  }
   
  // @ assert y >= t;*/
 
}

