int unknown();
void main21(){
	int x = 0;
	int y = 0;

	/*@
	loop invariant x == y * y;  
	loop invariant 0 <= y;  
	loop invariant 0 <= x;  
	loop invariant x >= y;  
	loop invariant x % y == 0;  
	loop invariant x == (y * (y - 1)) + y;
	loop invariant x == y * y;
	loop invariant 0 <= y;
	loop invariant 0 <= x;
	loop assigns y;
	loop assigns x;
	*/
	while(unknown()) {
		y = y + 1;
		x = y * y;
	}

	// @ assert x == y * y;*/
	return; 
}
