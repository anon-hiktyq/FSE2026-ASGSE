int unknown();
void main21(){
	int x = 0;
	int y = 0;

	/*@
	loop invariant x == (y * (y + 1)) / 2;
	loop invariant x % y == 0 || y == 0;
	loop invariant \forall integer k; 0 <= k < y ==> x == k * k || x == (k+1) * (k+1);
	loop invariant \exists integer k; k >= 0 && x == k * k;
	loop invariant \exists integer k; k == y && x == k * k;;
	loop invariant 0; <= y;
	loop invariant 0; <= x;
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
