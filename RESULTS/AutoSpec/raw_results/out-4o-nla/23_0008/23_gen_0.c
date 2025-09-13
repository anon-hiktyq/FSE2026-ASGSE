/*@
requires x >= 0 && x <= 10;
*/
int main23(int x) {
	
	int y = x * x;

	/*@
	loop invariant x >= 0 && x <= 10;
	loop invariant y >= x * x;
	loop invariant y >= 0;
	loop invariant \old(x) <= x;
	loop invariant y == \old(y) + (x - \old(x));
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

