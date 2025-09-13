int unknown();


void foo016(int i, int j) {
  
  int x = i;
  int y = j;
 
 
  /*@
  loop invariant x >= 0;
  loop invariant y == j - (i - x);
  loop invariant x == i - (j - y);
  loop invariant 0 <= i - x <= i;
  loop assigns x, y;
  */
  while(x != 0) {
	  x--;
	  y--;
  }

  // @ assert (i == j) ==> (y == 0);
}
