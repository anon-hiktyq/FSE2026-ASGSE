/*@
  requires x >= 0 && x <= 10;
*/
void hoo32(int x) {
	
	int y = x * x;

	/*@
	loop invariant y == x*x;
	loop invariant y == x * x;
	loop invariant y <= 1000;
	loop invariant x*x <= 1000;
	loop invariant x >= 0 && x <= 32;
	loop invariant x >= 0 && x <= 31;
	loop invariant x >= 0 && x <= 10;
	loop invariant x <= 11;
	loop invariant x <= 10;
	loop invariant x <= 1000;
	loop invariant x * x <= 1000;
	loop invariant 0 <= x;
	loop assigns y;
	loop assigns x;
	*/
	while(x * x <= 1000) {
		x = x + 1;
		y = y + 1;
	}

	/*@ assert y <= 1000; */
	return;
}

