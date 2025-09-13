
void foo04(int x,int y) {


  x = -50;
  
  /*@
  loop invariant x >= 0 || y > 0;
  loop invariant x <= -50 + (y * (y-1))/2;
  loop invariant x < y;
  loop invariant x < y * (y - 1) / 2;
  loop invariant x < y * (y + 51) / 2;
  loop invariant x < y * (y + 49) / 2;
  loop invariant x < 0;
  loop invariant x < 0 || y > 0;
  loop invariant x < 0 || x >= 0;
  loop invariant x < 0 || x >= 0 && y > 0;
  loop invariant x < 0 ==> y > 0;
  loop invariant 0 <= x + y;
  loop invariant 0 < y;
  loop invariant -50 <= x;
  loop assigns y;
  loop assigns x;
  */
  while( x < 0 ) {
	x = x + y;
	y++;
  }
  // @ assert y > 0;
}

