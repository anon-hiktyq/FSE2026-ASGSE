int unknown();

/*@ requires x != y;*/
void foo043(int x, int y) {
  int i=0;
  int t=y;
   
  

  /*@
  loop invariant x > 0 ==> y == t + i * x;
  loop invariant x <= 0 ==> y == t;
  loop invariant t <= y;
  loop invariant i >= 0;
  loop assigns i;
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

