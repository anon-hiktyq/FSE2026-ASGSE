int unknown();
int main21() {
	int x = 0;
	int y = 0;

	/*@
	loop invariant 0 <= y;
	loop invariant 0 <= x;
	loop invariant y * y == x;
	loop invariant \forall integer i; 0 <= i <= y ==> i * i <= x;
	loop invariant \exists integer k; 0 <= k <= y && x == k * k;
	loop invariant x % 2 == y % 2;
	loop invariant y <= x || x == y * y;
	loop invariant y >= 0 && x >= 0;
	loop invariant y <= x;
	loop invariant y <= x || y * y <= x;
	loop invariant y <= x || 0 <= y;
	loop invariant y <= x || 0 <= x;
	loop invariant y * y == x;
	loop invariant y * y <= x;
	loop invariant y * y <= x || 0 <= y;
	loop invariant y * y <= x || 0 <= x;
	loop invariant x == y * y;
	loop invariant x == y * y && x % 2 == y % 2;
	loop invariant x % 2 == y % 2;
	loop invariant \forall integer k; 0 <= k <= y ==> y * y >= k * k;
	loop invariant \forall integer k; 0 <= k <= y ==> x >= k*k;
	loop invariant \forall integer k; 0 <= k <= y ==> x >= k * k;
	loop invariant \forall integer k; 0 <= k <= y ==> k * k <= x;
	loop invariant \forall integer i; 0 <= i <= y ==> y * y >= i * i;
	loop invariant \forall integer i; 0 <= i < y ==> x >= i * i;
	loop invariant \exists integer k; 0 <= k <= y && x == k*k;
	loop invariant \exists integer k; 0 <= k <= y && x == k * k;
	loop invariant \exists integer k; 0 <= k <= y && k * k == x;
	loop invariant 0 <= y;
	loop invariant 0 <= y || 0 <= x;
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
