/*@
  requires x >= 0 && x <= 10;
*/
void hoo32(int x) {
	
	int y = x * x;

	/*@
	loop invariant y == x*x + (x - \old(x));
	loop invariant x*x <= 1000 || x*x > 1000;
	loop invariant \old(x) <= x;
	loop assigns y;
	loop assigns x;
	```c;
	```;
	The loop continues while `x * x <= 1000`. Since `sqrt(1000) ≈ 31.6`, the loop will terminate when `x` reaches 32 (since `32^2 = 1024 > 1000`).;
	Looking at this function, I need to analyze the loop behavior:;
	- Loop condition: `x * x <= 1000`;
	- Loop body: `x = x + 1` and `y = y + 1`;
	- Initially: `y = x * x` and `x` ranges from 0 to 10;
	*/
	while(x * x <= 1000) {
		x = x + 1;
		y = y + 1;
	}

	/*@ assert y <= 1000; */
	return;
}

