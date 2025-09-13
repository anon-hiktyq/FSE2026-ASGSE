/*@
requires x >= 0 && x <= 10;
*/
void main23(int x){
	
	int y = x * x;

	/*@
	loop invariant y >= x * x;
	loop invariant x >= 0;
	loop invariant y >= 0;
	loop invariant x <= 10 || y > 100;
	loop invariant y == (x * x) + ((x - \at(x, Pre)) * (2 * \at(x, Pre) + 1));
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

