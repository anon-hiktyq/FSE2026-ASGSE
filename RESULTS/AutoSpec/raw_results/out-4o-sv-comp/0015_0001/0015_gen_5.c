
/*@
requires y <= 1000000;
*/
void foo0015(int x, int y) {

	if (y > 0) {
		
		/*@
		loop invariant x < 100;
		loop invariant y > 0;
		loop invariant 0 <= x <= x + y;
		loop invariant x + y <= 1000000 + y;
		loop assigns x;
		*/
		while (x < 100) {
			x = x + y;
		}
	}

	// @ assert y <= 0 || (y > 0 && x >= 100);
}
