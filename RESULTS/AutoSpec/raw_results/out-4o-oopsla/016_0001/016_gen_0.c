int unknown();


void foo016(int i, int j) {
  
  int x = i;
  int y = j;
 
 
  /*@
  loop invariant x <= i;
  loop invariant y <= j;
  loop invariant (i - x) == (j - y);
  loop assigns x;
  loop assigns y;
  */
  while(x != 0) {
	  x--;
	  y--;
  }

  // @ assert (i == j) ==> (y == 0);
}
