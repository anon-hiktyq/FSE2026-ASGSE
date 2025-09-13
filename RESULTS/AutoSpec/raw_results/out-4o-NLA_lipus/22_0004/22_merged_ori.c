/*@
requires x >= 0;
*/
void main22(int x){
	
	int y = x * x;

	/*@
	loop invariant y == x * x;
	loop invariant y == x * x - (x - \at(x, Pre)) * (x - \at(x, Pre));
	loop invariant y == x * x - (2 * x) + 1;
	loop invariant y == x * x - (2 * x - 1);
	loop invariant y <= x * x;
	loop invariant y <= (x + 1) * (x + 1);
	loop invariant x * x <= y;
	loop invariant x * x - 2 * x + 1 <= y;
	loop invariant \at(x, Pre) <= x;
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

