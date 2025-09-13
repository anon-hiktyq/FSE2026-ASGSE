/*@
requires x >= 0 && x <= 10;
*/
int main23(int x) {
	
	int y = x * x;

	/*@
	loop invariant y == x * x;
	loop invariant y == x * x + (y - x * x);
	loop invariant y == \old(y) + (x - \old(x));
	loop invariant y <= x * x + (x - 10) * (x - 10);
	loop invariant y <= x * x + (x * 2) + 1;
	loop invariant y <= (x + 1) * (x + 1);
	loop invariant x >= 0 && y >= 0;
	loop invariant x >= 0 && x <= 10;
	loop invariant x * x <= y;
	loop invariant \old(x) <= x;
	loop invariant \forall integer k; x >= k ==> y >= k * k;
	loop invariant \forall integer k; x - k >= 0 ==> y - k >= x * x;
	loop invariant \forall integer k; 0 <= k ==> y >= x * x + k;
	loop invariant \exists integer k; y == x * x + k;
	loop invariant \exists integer k; y == k * k && k >= x;
	loop invariant 0 <= y;
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

