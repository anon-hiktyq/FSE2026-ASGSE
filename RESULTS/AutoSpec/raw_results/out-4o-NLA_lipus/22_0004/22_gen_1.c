/*@
requires x >= 0;
*/
void main22(int x){
	
	int y = x * x;

	/*@
	loop invariant y == x * x - (x - \at(x, Pre)) * (x - \at(x, Pre));
	loop invariant x >= \at(x, Pre);
	loop assigns x, y;
	*/
	while(unknown()) {
		x = x + 1;
		y = y + 1;
	}

	// @ assert y <= x * x;
	return; 
}

