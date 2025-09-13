/*@
requires x >= 0;
*/
void main22(int x){
	
	int y = x * x;

	/*@
	loop invariant y >= x * x;
	loop invariant y <= (x + 1) * (x + 1);
	loop assigns x, y;
	*/
	while(unknown()) {
		x = x + 1;
		y = y + 1;
	}

	// @ assert y <= x * x;
	return; 
}

