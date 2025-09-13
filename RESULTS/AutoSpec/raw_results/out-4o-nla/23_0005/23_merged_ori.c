/*@
requires x >= 0 && x <= 10;
*/
int main23(int x) {
	
	int y = x * x;

	/*@
	loop invariant y == x * x || y > x * x;
	loop invariant y == x * x + (x - \old(x));
	loop invariant y == x * x + (x - \at(x, Pre));
	loop invariant y == (x * x) + \count(unknown);
	loop invariant y <= x * x + 10;
	loop invariant y <= x * x + (x - x * x);;
	loop invariant y <= (x + 1) * (x + 1);
	loop invariant x >= 0 && x <= 10;
	loop invariant x <= 10 || y > 100;
	loop invariant x * x <= y;
	loop invariant \old(y) <= y;
	loop invariant \old(x) <= x;
	loop invariant \forall integer k; \at(x, Pre) <= k <= x ==> y >= k * k;
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

