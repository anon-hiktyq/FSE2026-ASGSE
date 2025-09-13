/*@
requires x >= 0 && x <= 10;
*/
void main23(int x){
	
	int y = x * x;

	/*@
	loop invariant y == x * x;
	loop invariant y == (x - \at(x, Pre)) * (x - \at(x, Pre)) + \at(y, Pre);
	loop invariant y == (x * x) - (\at(x, Pre) * \at(x, Pre)) + \at(y, Pre);
	loop invariant x >= 0 && x <= 10;
	loop invariant x <= 10;
	loop invariant x * x <= y;
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

