
void foo04(int x,int y) {


  x = -50;
  
  /*@
  loop invariant x < y * (y + 51) / 2; 
  loop invariant x < 0;
  loop invariant x < -50 + (y + 49) * (y - 50) / 2; 
  loop invariant y > 0;
  loop invariant y >= 1;
  loop assigns x;
  loop assigns y;
  */
  while( x < 0 ) {
	x = x + y;
	y++;
  }
  // @ assert y > 0;
}

