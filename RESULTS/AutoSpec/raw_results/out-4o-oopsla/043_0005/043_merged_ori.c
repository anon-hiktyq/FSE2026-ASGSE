int unknown();

/*@ requires x != y;*/
void foo043(int x, int y) {
  int i=0;
  int t=y;
   
  

  /*@
  loop invariant y == t || y > t;
  loop invariant x >= 0 ==> y >= t;;
  loop invariant x > 0 ==> y == t + i * x;
  loop invariant x <= 0 ==> y == t;;
  loop invariant x != y;
  loop invariant x != 0;
  loop invariant \forall integer k; k >= 0 ==> (x > 0 ==> y >= t + k * x);
  loop invariant \forall integer k; 0 <= k < i ==> x > 0 ==> y >= k*x + t;
  loop invariant \forall integer k; 0 <= k < i ==> x != k;
  loop invariant \forall integer k; (x > 0 ==> y == t + k * x) && (x <= 0 ==> y == t);;
  loop invariant \exists integer k; k >= 0 && y == t + k * x;
  loop invariant 0 <= i;
  loop invariant 0 < i;
  loop invariant (x > 0 ==> y >= t + i * x);
  loop invariant (x <= 0 ==> y == t);
  loop invariant x > 0 ==> y >= t;
  loop invariant x <= 0 ==> y == t;
  loop invariant t == y || y > t;
  loop invariant t <= y;
  loop assigns y;
  */
  while (unknown()){
    if (x > 0)   
      y = y + x;
  }
   
  // @ assert y >= t;*/
 
}

