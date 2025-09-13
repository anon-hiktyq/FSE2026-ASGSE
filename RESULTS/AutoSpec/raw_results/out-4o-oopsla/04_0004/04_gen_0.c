
void foo04(int x,int y) {


  x = -50;
  
  /*@
  loop invariant x < 0 ==> y > 0;
  loop invariant x >= -50;
  loop invariant x < y;
  loop invariant y > 0;
  loop assigns x;
  loop assigns y;
  */
  while( x < 0 ) {
	x = x + y;
	y++;
  }
  // @ assert y > 0;
}

