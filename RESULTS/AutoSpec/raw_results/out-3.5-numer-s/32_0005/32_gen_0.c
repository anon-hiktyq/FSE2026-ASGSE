/*@
  requires x >= 0 && x <= 10;
*/
void hoo32(int x) {
	
	int y = x * x;

	/*@
	loop invariant x >= 0;
	loop invariant y >= 0;
	loop invariant x*x > 1000 ==> y <= 1000;
	loop assigns x;
	loop assigns y;
	*/
	while(x * x <= 1000) {
		x = x + 1;
		y = y + 1;
	}

	/*@ assert y <= 1000; */
	return;
}

