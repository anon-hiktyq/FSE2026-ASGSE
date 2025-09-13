int unknown();


void foo016(int i, int j) {
  
  int x = i;
  int y = j;
 
 
  /*@
  loop invariant y == j - (i - x);
  loop invariant y <= j;
  loop invariant x == y + (i - j);
  loop invariant x == i - (j - y);
  loop invariant x == 0 || y == j - (i - x);
  loop invariant x <= i;
  loop invariant x - y == i - j;
  loop invariant i - x == j - y;
  loop invariant 0 <= i - x;
  loop invariant (i - x) == (j - y);
  loop assigns y;
  loop assigns x;
  */
  while(x != 0) {
	  x--;
	  y--;
  }

  //@ assert (i == j) ==> (y == 0);
}
