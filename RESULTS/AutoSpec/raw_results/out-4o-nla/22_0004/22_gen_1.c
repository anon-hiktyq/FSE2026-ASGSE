/*@
requires x >= 0;
*/
int main22(int x) {
	
	int y = x * x;

	/*@
	loop invariant y >= x * x;
	loop invariant y >= 0;
	loop invariant x >= 0;
	loop invariant y - x * x >= 0;
	loop invariant y - x * x <= 1;
	loop invariant 0 <= x;
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

