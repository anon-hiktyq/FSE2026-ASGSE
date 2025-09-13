
void foo04(int x,int y) {


  x = -50;
  
  /*@
  loop invariant x >= -50;
  loop invariant y == 0 ==> x == -50;
  loop invariant x < y * (y + 1) / 2;
  loop invariant \forall integer k; 0 <= k < y ==> x <= k * (k + 1) / 2;
  loop invariant x < 0 || x >= 0;
  loop invariant y > 0;
  loop invariant x <= -50 + y*(y-1)/2;
  loop invariant x < y*y;
  loop invariant x < y * y;
  loop invariant x < 0 || x >= 0;
  loop invariant \forall integer k; 0 <= k < y ==> k >= 0;
  loop assigns y;
  loop assigns x;
  */
  while( x < 0 ) {
	x = x + y;
	y++;
  }
  // @ assert y > 0;
}

