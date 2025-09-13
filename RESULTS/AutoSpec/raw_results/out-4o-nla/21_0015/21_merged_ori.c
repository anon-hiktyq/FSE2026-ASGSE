int unknown();
int main21() {
	int x = 0;
	int y = 0;

	/*@
	loop invariant x == (y - 1) * (y - 1) + 2 * (y - 1) + 1;
	loop invariant \forall integer z; 0 <= z <= y ==> x == z * z;
	loop invariant \forall integer k; 0 <= k <= y ==> x == k * k;
	loop invariant \forall integer k; 0 <= k <= y ==> k * k <= x;
	loop invariant \forall integer k; 0 <= k < y ==> x == k * k;
	loop invariant \forall integer k; 0 <= k < y ==> x == k * k + 2 * k + 1;
	loop invariant \exists integer k; k == y && x == k * k;
	loop invariant \exists integer k; k * k == x && k == y;
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
	return 0;
}
