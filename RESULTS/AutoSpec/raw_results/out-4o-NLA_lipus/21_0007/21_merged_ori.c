int unknown();
void main21(){
	int x = 0;
	int y = 0;

	/*@
	loop invariant y <= x;
	loop invariant x == y * y;;
	loop invariant x == (y * (y - 1)) + y;
	loop invariant x == (y * (y + 1)) / 2;;
	loop invariant x == (y * (y + 1)) - y;
	loop invariant x % y == 0;
	loop invariant \forall integer k; 0 <= k <= y ==> x >= k * k;
	loop invariant \forall integer k; 0 <= k < y ==> x == k*k;
	loop invariant \forall integer k; 0 <= k < y ==> x == (k + 1) * (k + 1);
	loop invariant 0; <= x;
	loop invariant 0 <= y;;
	loop invariant 0 <= x;
	loop invariant x == y * y;
	loop invariant 0 <= y;
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
