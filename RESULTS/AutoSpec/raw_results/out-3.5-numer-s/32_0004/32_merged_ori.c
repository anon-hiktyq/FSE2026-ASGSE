/*@
  requires x >= 0 && x <= 10;
*/
void hoo32(int x) {
	
	int y = x * x;

	/*@
	loop invariant y == \old(x) * \old(x) + (x - \old(x));
	loop invariant x * x > 1000 ==> y <= 1000;
	loop invariant \old(x) <= x;
	loop invariant \old(x) * \old(x) <= y;
	loop assigns y;
	loop assigns x;
	```c;
	```;
	The key relationships are:;
	Looking at this function, I need to analyze the loop behavior:;
	- `y` increases by 1 each iteration;
	- `x` increases by 1 each iteration;
	- The loop terminates when `x * x > 1000`;
	- Loop continues while `x * x <= 1000`;
	- Initially: `y = x * x`;
	- Initially `y = x * x`, but after the first iteration this relationship changes;
	- In each iteration: `x = x + 1` and `y = y + 1`;
	*/
	while(x * x <= 1000) {
		x = x + 1;
		y = y + 1;
	}

	/*@ assert y <= 1000; */
	return;
}

