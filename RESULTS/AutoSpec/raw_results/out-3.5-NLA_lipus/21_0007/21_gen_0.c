int unknown();
void main21(){
	int x = 0;
	int y = 0;

	/*@
	Looking at this code, I need to generate additional loop invariants that differ from the existing ones. The existing invariants are:
	
	- `y <= x`
	- `y * y == x` 
	- `x == y * y`
	- `0 <= y`
	- `0 <= x`
	
	Here are additional diverse loop invariants:
	
	```
	loop invariant x >= 0;
	loop invariant y >= 0;
	loop invariant x - y >= 0;
	loop invariant y == 0 ==> x == 0;
	loop invariant x == 0 ==> y == 0;
	loop invariant y > 0 ==> x > 0;
	loop invariant x >= y;
	loop invariant y * (y + 1) > x || y == 0;
	```
	loop invariant y <= x;
	loop invariant y * y == x;
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
