/*@
requires x >= 0;
*/
void main22(int x){
	
	int y = x * x;

	/*@
	loop invariant y == x * x - ((x * x) - y);
	loop invariant y == (x - 1) * (x - 1) + 2 * (x - 1) + 1;
	loop invariant y == (x * (x - 1)) + 1;
	loop invariant y - x == (x - 1) * (x - 1);
	loop invariant y - x == (x * x - x);
	loop invariant y - x * x == x - (x - y);
	loop invariant y - x * x == 0;
	loop invariant x * x <= y;
	loop invariant 0 <= y;
	loop invariant y == x * x - (x * x - y);
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

