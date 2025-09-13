int unknown();

/*@ requires x != y;*/
void foo043(int x, int y) {
  int i=0;
  int t=y;
   
  

  /*@
  loop invariant y != t || (x > 0);
  loop invariant y >= t;
  loop assigns y;
  */
  while (unknown()){
    if (x > 0)   
      y = y + x;
  }
   
  // @ assert y >= t;*/
 
}

