int unknown();

/*@ requires x != y;*/
void foo043(int x, int y) {
  int i=0;
  int t=y;
   
  

  /*@
  loop invariant x != 0;
  loop invariant y >= t;
  loop invariant x > 0 ==> y == t + i * x;
  loop invariant \forall integer k; 0 <= k < i ==> x > 0 ==> y >= t + k * x;
  loop invariant y >= t || x > 0;
  loop invariant t <= y;
  loop assigns y;
  */
  while (unknown()){
    if (x > 0)   
      y = y + x;
  }
   
  // @ assert y >= t;*/
 
}

