/*@
requires x >= 0;
*/
int main22(int x) {
	
	int y = x * x;

	/*@
	loop invariant y >= x * x;
	loop invariant x >= 0;
	loop invariant y == (x - x_initial) + x_initial * x_initial;
	loop invariant 0 <= x - x_initial;
	loop invariant \forall integer k; 0 <= k <= x_initial ==> y >= k * k;
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

