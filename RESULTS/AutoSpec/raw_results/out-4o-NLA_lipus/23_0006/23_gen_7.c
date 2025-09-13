/*@
requires x >= 0 && x <= 10;
*/
void main23(int x){
	
	int y = x * x;

	/*@
	loop invariant x >= 0 && x <= 10;
	loop invariant y == (x - \at(x, Pre)) * (x - \at(x, Pre)) + \at(y, Pre);
	loop assigns x, y;
	*/
	while(unknown()) {
		x = x + 1;
		y = y + 1;
	}

	// @ assert y <= x * x;
	return; 
}

