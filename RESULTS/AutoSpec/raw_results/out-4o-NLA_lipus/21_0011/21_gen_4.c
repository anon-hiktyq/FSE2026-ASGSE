int unknown();
void main21(){
	int x = 0;
	int y = 0;

	/*@
	loop invariant x >= y * y;
	loop invariant x == y * y;
	loop invariant \forall integer k; 0 <= k < y ==> x >= k * k;
	loop invariant y >= 0;
	loop invariant x >= 0;
	loop invariant \exists integer k; 0 <= k <= y && x == k * k;
	loop invariant \forall integer k; 0 <= k < y ==> x == k * k + (y - k - 1) * (y - k - 1);
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
