/*@
requires x >= 0 && x <= 10;
*/
void main23(int x){
	
	int y = x * x;

	/*@
	loop invariant y >= x * x - 2 * x + 1;
	loop invariant y <= x * x;
	loop invariant x >= 0;
	loop invariant \exists integer k; k == x && y == k * k;
	loop invariant y == x * x - 2 * x + 1 + \at(y, LoopEntry) - \at(x * x, LoopEntry);
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

