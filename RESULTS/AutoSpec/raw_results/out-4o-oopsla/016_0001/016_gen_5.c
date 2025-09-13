int unknown();


void foo016(int i, int j) {
  
  int x = i;
  int y = j;
 
 
  /*@
  loop invariant x >= 0;
  loop invariant y == j - (i - x);
  loop invariant 0 <= x <= i;
  loop invariant i - x == j - y;
  loop assigns x;
  loop assigns y;
  */
  while(x != 0) {
	  x--;
	  y--;
  }

  // @ assert (i == j) ==> (y == 0);
}
