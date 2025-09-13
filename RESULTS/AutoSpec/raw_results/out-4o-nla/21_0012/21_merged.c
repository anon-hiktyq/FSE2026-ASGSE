int unknown();
int main21() {
	int x = 0;
	int y = 0;

	/*@
	loop invariant y == \sqrt(x);
	loop invariant y <= x;
	loop invariant x == (y-1) * (y-1) + 2*(y-1) + 1;
	loop invariant x <= y * y;
	loop invariant \forall integer n; 0 <= n < y ==> (n*n <= x);
	loop invariant \forall integer k; 0 <= k < y ==> x >= k * k;
	loop invariant \exists integer n; x == n * n && y == n;
	loop invariant \exists integer k; 0 <= k <= y && x == k * k;
	loop invariant x == y * y;
	loop invariant 0 <= y;
	loop invariant 0 <= x;
	loop assigns y;
	loop assigns x;
	*/
	while(unknown()) {
		y = y + 1;
		x = y * y;
	}

	//@ assert x == y * y;*/
	return 0;
}
