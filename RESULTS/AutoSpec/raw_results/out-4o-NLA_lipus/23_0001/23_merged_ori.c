/*@
requires x >= 0 && x <= 10;
*/
void main23(int x){
	
	int y = x * x;

	/*@
	loop invariant y == \old(x * x) + (x - \old(x)) + (\sum integer k; \old(x) <= k < x; 1);
	loop invariant y == (x - (\at(x, LoopEntry) - \at(y, LoopEntry))) * (\at(x, LoopEntry) - \at(y, LoopEntry)) + \at(y, LoopEntry);
	loop invariant y == (x * x) - (\old(x) * \old(x)) + \old(y);
	loop invariant x >= 0 && x <= 10;
	loop invariant x * x <= y;
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

