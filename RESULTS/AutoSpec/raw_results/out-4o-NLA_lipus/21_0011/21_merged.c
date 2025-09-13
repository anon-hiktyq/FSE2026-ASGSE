int unknown();
void main21(){
	int x = 0;
	int y = 0;

	/*@
	loop invariant y <= x;
	loop invariant y <= x || y * y <= x;
	loop invariant y < x;
	loop invariant y * y == x;
	loop invariant y * y <= x;
	loop invariant y * y < x;
	loop invariant y * y < x;
	loop invariant y * y < x;
	loop invariant y * y < x;
	loop invariant y * y < x;
	loop invariant y * y < x;
	loop invariant y * y < x;
	loop invariant y * y < x;
	loop invariant x <= (y + 1) * (y + 1) - 1;
	loop invariant x <= (y + 1) * (y + 1) - 1 || y <= x;
	loop invariant x <= (y + 1) * (y + 1) - 1 || y * y <= x;
	loop invariant x <= (y + 1) * (y + 1) - 1 || 0 <= y;
	loop invariant x <= (y + 1) * (y + 1) - 1 || 0 <= x;
	loop invariant x <= (y + 1) * (y + 1) - 1 || (y - 1) * (y - 1) <= x;
	loop invariant x <= (y + 1) * (y + 1) - 1 || (y - 1) * (y - 1) <= x;
	loop invariant x < (y + 1) * (y + 1) - 1;
	loop invariant x % y == 0;
	loop invariant \forall integer k; 0 <= k <= y ==> x >= k * k;
	loop invariant \forall integer k; 0 <= k <= y ==> x == k * k || x > k * k;
	loop invariant 0 <= y || y <= x;
	loop invariant 0 <= y || y * y <= x;
	loop invariant 0 <= y || 0 <= x;
	loop invariant 0 <= y || (y - 1) * (y - 1) <= x;
	loop invariant 0 <= x || y <= x;
	loop invariant 0 <= x || y * y <= x;
	loop invariant 0 <= x || (y - 1) * (y - 1) <= x;
	loop invariant (y - 1) * (y - 1) <= x;
	loop invariant (y - 1) * (y - 1) <= x || y <= x;
	loop invariant (y - 1) * (y - 1) <= x || y <= x;
	loop invariant (y - 1) * (y - 1) <= x || y * y <= x;
	loop invariant (y - 1) * (y - 1) <= x || y * y <= x;
	loop invariant (y - 1) * (y - 1) <= x || 0 <= y;
	loop invariant (y - 1) * (y - 1) <= x || 0 <= x;
	loop invariant (y - 1) * (y - 1) <= x || (y - 1) * (y - 1) <= x;
	loop invariant (y - 1) * (y - 1) < x;
	loop invariant x == y * y;
	loop invariant \forall integer k; 0 <= k < y ==> x >= k * k;
	loop invariant \exists integer k; 0 <= k <= y && x == k * k;
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
