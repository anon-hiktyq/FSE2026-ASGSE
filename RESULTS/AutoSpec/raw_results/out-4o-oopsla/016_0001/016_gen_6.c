int unknown();


void foo016(int i, int j) {
  
  int x = i;
  int y = j;
 
 
  /*@
  loop invariant x <= i;
  loop invariant y == j - (i - x);
  loop invariant x >= 0;
  loop invariant x == y + (i - j);
  loop assigns x, y;
  */
  while(x != 0) {
	  x--;
	  y--;
  }

  // @ assert (i == j) ==> (y == 0);
}
