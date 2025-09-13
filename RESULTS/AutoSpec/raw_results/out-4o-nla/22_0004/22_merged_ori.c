/*@
requires x >= 0;
*/
int main22(int x) {
	
	int y = x * x;

	/*@
	loop invariant y == x * x;
	loop invariant y == x * x + (x - \old(x));
	loop invariant y == (x - x_initial) + x_initial * x_initial;
	loop invariant y == (x - 1) * (x - 1) + 1;
	loop invariant y - x * x <= 1;
	loop invariant x <= y;
	loop invariant x * x; <= y;
	loop invariant x * x <= y;
	loop invariant \forall integer k; y >= k * k ==> k <= x;
	loop invariant \forall integer k; k >= 0 ==> y >= k;
	loop invariant \forall integer k; 0 <= k <= x_initial ==> y >= k * k;
	loop invariant \exists integer k; y == k * k && k >= x;
	loop invariant \exists integer k; k >= 0 && y == k * k;
	loop invariant 0; <= y;
	loop invariant 0; <= x;
	loop invariant 0 <= y;
	loop invariant 0 <= y - x * x;
	loop invariant 0 <= x - x_initial;
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

