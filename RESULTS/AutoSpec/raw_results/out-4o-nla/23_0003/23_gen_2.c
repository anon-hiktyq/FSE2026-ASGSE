/*@
requires x >= 0 && x <= 10;
*/
int main23(int x) {
	
	int y = x * x;

	/*@
	loop invariant y >= x * x - 2 * x;
	loop invariant x >= 0;
	loop invariant y >= 0;
	loop invariant x <= 10 || (x > 10 && y >= x * x);
	loop invariant y >= x * x && y - x * x >= 0;
	loop assigns y;
	loop assigns x;
	*/
	while(unknown()) {
		x = x + 1;
		y = y + 1;
	}

	// @ assert y <= x * x;
	return 0;
}

