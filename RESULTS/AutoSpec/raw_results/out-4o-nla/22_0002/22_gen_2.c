/*@
requires x >= 0;
*/
int main22(int x) {
	
	int y = x * x;

	/*@
	loop invariant y >= x * x;
	loop invariant x >= 0;
	loop invariant y == x * x + (x - \at(x, Pre));
	loop invariant \exists integer k; k >= 0 && x == \at(x, Pre) + k && y == (\at(x, Pre) + k) * (\at(x, Pre) + k);
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

