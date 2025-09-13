/*@
requires x >= 0;
*/
void main22(int x){
	
	int y = x * x;

	/*@
	loop invariant y <= x * x;
	loop invariant y >= 0;
	loop invariant x >= 0;
	loop assigns x;
	loop assigns y;
	*/
	while(unknown()) {
		x = x + 1;
		y = y + 1;
	}

	// @ assert y <= x * x;
	return; 
}

