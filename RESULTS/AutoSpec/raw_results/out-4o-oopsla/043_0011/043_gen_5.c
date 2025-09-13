int unknown();

/*@ requires x != y;*/
void foo043(int x, int y) {
  int i=0;
  int t=y;
   
  

  /*@
  loop invariant x != 0;
  loop invariant y == t + i * x || y >= t + i * x;
  loop invariant x > 0 ==> y >= t + x * i;
  loop invariant t <= y;
  loop invariant i >= 0;
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

