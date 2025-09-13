int unknown();
int main21() {
	int x = 0;
	int y = 0;

	/*@
	loop invariant x == y * y;
	loop invariant 0 <= y;
	loop invariant 0 <= x;
	loop invariant y <= x;
	loop invariant \forall integer k; 0 <= k < y ==> k*k <= x;
	loop invariant \exists integer k; 0 <= k <= y && x == k * k;
	loop invariant x == y * y;
	loop invariant x == (y * y);
	loop invariant x % y == 0 || y == 0;
	loop invariant \forall integer k; 0 <= k < y ==> k*k <= x;
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
	return 0;
}
