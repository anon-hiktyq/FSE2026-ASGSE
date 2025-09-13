/*@
requires x >= 0 && x <= 10;
*/
void main23(int x){
	
	int y = x * x;

	/*@
	loop invariant y == x * x || y > x * x;
	loop invariant y == x * x - 2 * x + 1 + \at(y, LoopEntry) - \at(x * x, LoopEntry);
	loop invariant y == x * x + (x % 2);
	loop invariant y == (x * x) + (x - \at(x, Pre));
	loop invariant y == (x * x) + ((x - \at(x, Pre)) * (2 * \at(x, Pre) + 1));
	loop invariant y <= x * x;
	loop invariant y <= (x + 1) * (x + 1);
	loop invariant x >= 0 && x <= 10;
	loop invariant x <= \at(x, Pre) + 10;
	loop invariant x <= 10;
	loop invariant x <= 10 || y > 100;
	loop invariant x * x <= y;
	loop invariant x * x - 2 * x + 1 <= y;
	loop invariant x % 2 == 0 || y % 2 == 1;
	loop invariant \exists integer k; k >= 0 && x == \at(x, Pre) + k;
	loop invariant \exists integer k; k == x && y == k * k;
	loop invariant \at(x, Pre) <= x;
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
	return; 
}

