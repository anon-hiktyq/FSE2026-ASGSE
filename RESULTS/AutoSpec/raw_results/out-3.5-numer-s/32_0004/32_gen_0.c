/*@
  requires x >= 0 && x <= 10;
*/
void hoo32(int x) {
	
	int y = x * x;

	/*@
	Looking at this function, I need to analyze the loop behavior:
	
	- Initially: `y = x * x`
	- In each iteration: `x = x + 1` and `y = y + 1`
	- Loop continues while `x * x <= 1000`
	
	The key relationships are:
	- `x` increases by 1 each iteration
	- `y` increases by 1 each iteration  
	- Initially `y = x * x`, but after the first iteration this relationship changes
	- The loop terminates when `x * x > 1000`
	
	```c
	loop invariant x >= \old(x);
	loop invariant y >= \old(x) * \old(x);
	loop invariant y == \old(x) * \old(x) + (x - \old(x));
	loop invariant x * x > 1000 ==> y <= 1000;
	loop assigns x;
	loop assigns y;
	```
	*/
	while(x * x <= 1000) {
		x = x + 1;
		y = y + 1;
	}

	/*@ assert y <= 1000; */
	return;
}

