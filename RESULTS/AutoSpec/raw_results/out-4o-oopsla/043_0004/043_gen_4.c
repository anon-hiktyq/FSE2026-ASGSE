int unknown();

/*@ requires x != y;*/
void foo043(int x, int y) {
  int i=0;
  int t=y;
   
  

  /*@
  loop invariant y >= t;  
  loop invariant x != y; 
  loop invariant t <= y; 
  loop invariant \forall integer k; t <= k <= y ==> k % x != 0;
  loop invariant t <= y;
  loop assigns y;
  */
  while (unknown()){
    if (x > 0)   
      y = y + x;
  }
   
  // @ assert y >= t;*/
 
}

