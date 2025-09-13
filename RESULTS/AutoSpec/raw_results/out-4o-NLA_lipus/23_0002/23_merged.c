/*@
requires x >= 0 && x <= 10;
*/
void main23(int x){
	
	int y = x * x;

	/*@
	loop invariant y == x * x || y > x * x;
	loop invariant y == x * x + (y - x * x);
	loop invariant y <= x * x + (x + 1);
	loop invariant y <= (x + 1) * (x + 1);
	loop invariant x >= 0 && x <= 10;
	loop invariant x <= y;
	loop invariant x * x <= y;
	loop invariant \forall integer k; 0 <= k <= x ==> y >= k * k;
	loop invariant \exists integer k; 0 <= k <= x && y == k * k;
	loop invariant 0 <= y;
	loop invariant 0 <= x;
	loop invariant 0 <= x + y;
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

