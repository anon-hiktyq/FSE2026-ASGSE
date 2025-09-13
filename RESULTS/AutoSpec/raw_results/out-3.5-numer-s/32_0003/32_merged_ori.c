/*@
  requires x >= 0 && x <= 10;
*/
void hoo32(int x) {
	
	int y = x * x;

	/*@
	loop invariant y == \old(y) + (x - \old(x));
	loop invariant x*x > 1000 ==> false;
	loop invariant 0 <= y;
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

