int unknown();

/*@ requires x != y;*/
void foo043(int x, int y) {
  int i=0;
  int t=y;
   
  

  /*@
  loop invariant y == t + i * x;
  loop invariant x > 0 ==> y >= t;
  loop invariant x > 0 ==> y > t;;
  loop invariant x <= 0 ==> y == t;;
  loop invariant x <= 0 ==> y == t;
  loop invariant x != y;;
  loop invariant x != y;
  loop invariant x != 0 ==> y % x == t % x;
  loop invariant t; <= y;
  loop invariant t == y || y > t;
  loop invariant t <= y;;
  loop invariant \forall integer k; t <= k <= y ==> k % x != 0;
  loop invariant \forall integer k; k >= 0 ==> y == t + k * x;
  loop invariant t <= y;
  loop assigns y;
  */
  while (unknown()){
    if (x > 0)   
      y = y + x;
  }
   
  // @ assert y >= t;*/
 
}

