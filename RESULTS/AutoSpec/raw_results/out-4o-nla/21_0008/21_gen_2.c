int unknown();
int main21() {
	int x = 0;
	int y = 0;

	/*@
	loop invariant x == y * y;
	loop invariant 0 <= x;
	loop invariant 0 <= y;
	loop invariant \forall integer i; 0 <= i < y ==> x >= i * i;
	loop invariant x >= 0;
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

	// @ assert x == y * y;*/
	return 0;
}
