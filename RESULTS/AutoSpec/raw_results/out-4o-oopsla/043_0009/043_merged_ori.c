int unknown();

/*@ requires x != y;*/
void foo043(int x, int y) {
  int i=0;
  int t=y;
   
  

  /*@
  loop invariant y == t + i * x;
  loop invariant y - t == i * x;
  loop invariant y != t || i == 0;
  loop invariant x > 0 || y == t;
  loop invariant x > 0 ==> y >= t + i * x;
  loop invariant x > 0 ==> y > t;
  loop invariant x <= 0 ==> y == t;
  loop invariant x != 0;
  loop invariant x != 0 && t <= y;
  loop invariant unknown() ==> y >= t;
  loop invariant t == y - i*x;;
  loop invariant i == 0;
  loop invariant 0 <= i;
  loop invariant (x > 0) ==> y >= t;
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

