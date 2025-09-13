int unknown();
void main21(){
	int x = 0;
	int y = 0;

	/*@
	loop invariant y > 0 ==> x > 0;
	loop invariant y == 0 || x >= 1;
	loop invariant y == 0 ==> x == 0;
	loop invariant y * y == x;
	loop invariant x >= y * 2 - 1 || y <= 1;
	loop invariant x == y + y * (y - 1);
	loop invariant 0 <= x - y;
	loop invariant 0 < x - y;
	loop invariant y >= 0 ==> x >= 0;
	loop invariant y <= x;
	loop invariant y <= x || y == 0;
	loop invariant x == y * y;
	loop invariant x % 2 == 0 || y % 2 == 1;
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
