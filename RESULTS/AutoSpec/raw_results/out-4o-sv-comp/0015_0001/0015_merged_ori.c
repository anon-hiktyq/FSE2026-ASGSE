
/*@
requires y <= 1000000;
*/
void foo0015(int x, int y) {

	if (y > 0) {
		
		/*@
		loop invariant y <= x;
		loop invariant y <= 1000000;
		loop invariant x >= 100 || x < 100;
		loop invariant x <= x + y;
		loop invariant x <= 100 + y * (\at(x, Pre) - x)/y;
		loop invariant x < 100;
		loop invariant x < 1000000;
		loop invariant x < 100 || x >= 100;
		loop invariant x < 100 ==> y > 0;
		loop invariant x < 100 ==> x + y >= x;
		loop invariant x + y <= 1000000 + y;
		loop invariant \at(x, Pre) <= x;
		loop invariant 0 >= y || x >= 100;
		loop invariant 0 <= x;
		loop invariant 0 < y;
		loop invariant 0 < y ==> x <= 1000000;
		loop assigns x;
		*/
		while (x < 100) {
			x = x + y;
		}
	}

	// @ assert y <= 0 || (y > 0 && x >= 100);
}
