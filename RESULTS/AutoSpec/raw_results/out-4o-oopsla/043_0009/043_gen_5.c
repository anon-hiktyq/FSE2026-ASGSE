int unknown();

/*@ requires x != y;*/
void foo043(int x, int y) {
  int i=0;
  int t=y;
   
  

  /*@
  loop invariant x > 0 ==> y > t;
  loop invariant x <= 0 ==> y == t;
  loop invariant x != 0;
  loop invariant t == y - i*x; 
  loop assigns i;
  loop assigns y;
  loop invariant t <= y;
  loop assigns y;
  loop assigns i;
  */
  while (unknown()){
    if (x > 0)   
      y = y + x;
  }
   
  // @ assert y >= t;*/
 
}

