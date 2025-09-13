/*@
requires x >= 0 && x <= 10;
*/
int main23(int x) {
	
	int y = x * x;

	/*@
	loop invariant y >= x * x && y - x * x >= 0;
	loop invariant y == x * x - (x - \at(x, Pre)) * (x - \at(x, Pre));
	loop invariant y <= x * x + (x - 1);
	loop invariant y <= (x + 1) * (x + 1);
	loop invariant x >= 0 && x <= 10;
	loop invariant x <= 10;
	loop invariant x <= 10 || (x > 10 && y >= x * x);
	loop invariant x <= 10 + (\at(x, Pre) - x);
	loop invariant x * x <= y;
	loop invariant x * x - 2 * x <= y;
	loop invariant x * x - (2 * x + 1) <= y;
	loop invariant \forall integer k; x - k >= 0 ==> y >= k * k;
	loop invariant \at(x, Pre) <= x;
	loop invariant \at(x, Pre) * \at(x, Pre) <= y;
	loop invariant 0 <= y;
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

