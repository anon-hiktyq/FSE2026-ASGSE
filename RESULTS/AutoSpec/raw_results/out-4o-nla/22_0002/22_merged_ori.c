/*@
requires x >= 0;
*/
int main22(int x) {
	
	int y = x * x;

	/*@
	loop invariant y == x * x;;
	loop invariant y == x * x + (x - \at(x, Pre));
	loop invariant y == (x - \at(x, Pre)) * (x - \at(x, Pre)) + \at(y, Pre);;
	loop invariant y == (x * x) + (y - x * x);;
	loop invariant y == (x * x) + (y - x * x);
	loop invariant y == (x * x) + (x - \at(x, Pre));
	loop invariant y <= (x + 1) * (x + 1);
	loop invariant y - x * x <= 2 * x + 1;
	loop invariant y % 2 == (x * x) % 2;;
	loop invariant x <= y;
	loop invariant x * x; <= y;
	loop invariant x * x <= y;
	loop invariant \exists integer k; k >= 0 && y == x * x + k;
	loop invariant \exists integer k; k >= 0 && y == k * k;
	loop invariant \exists integer k; k >= 0 && x == \at(x, Pre) + k && y == (\at(x, Pre) + k) * (\at(x, Pre) + k);
	loop invariant 1 <= y;
	loop invariant 0; <= y;
	loop invariant 0; <= x;
	loop invariant 0 <= y;
	loop invariant 0 <= y - x * x;
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

