int unknown();
int main21() {
	int x = 0;
	int y = 0;

	/*@
	loop invariant y <= x;
	loop invariant y <= x || 1 <= x;
	loop invariant y <= x || 0 <= y;
	loop invariant y <= x || 0 <= x;
	loop invariant y < x;
	loop invariant x >= 0 && y >= 0;
	loop invariant x == (y * y);;
	loop invariant x <= y*y;
	loop invariant x <= y*y || y <= x;
	loop invariant x <= y*y || 1 <= x;
	loop invariant x <= y*y || 0 <= y;
	loop invariant x <= y*y || 0 <= x;
	loop invariant x <= y*y || (y-1)*(y-1) <= x;
	loop invariant x < y*y;
	loop invariant x % y == 0 || y == 0;;
	loop invariant \forall integer k; 0 <= k <= y ==> k*k <= x;
	loop invariant \forall integer k; 0 <= k < y ==> k*k <= x;;
	loop invariant \forall integer k; 0 <= k < y ==> k * k <= x;
	loop invariant \exists integer k; 0 <= k <= y ==> x == k * k;
	loop invariant \exists integer k; 0 <= k <= y && x == k * k;;
	loop invariant 1; <= x;
	loop invariant 1; < x;
	loop invariant 1; < x;
	loop invariant 1; < x;
	loop invariant 1; < x;
	loop invariant 1; < x;
	loop invariant 1; < x;
	loop invariant 1; < x;
	loop invariant 1; < x;
	loop invariant 1; < x;
	loop invariant 1; < x;
	loop invariant 0 <= y;;
	loop invariant 0 <= y || 1 <= x;
	loop invariant 0 <= y || 0 <= x;
	loop invariant 0 <= x;;
	loop invariant 0 <= x || 1 <= x;
	loop invariant 0 <= x % (y + 1);
	loop invariant 0 <= x % (y + 1) || y <= x;
	loop invariant 0 <= x % (y + 1) || x <= y*y;
	loop invariant 0 <= x % (y + 1) || 1 <= x;
	loop invariant 0 <= x % (y + 1) || 0 <= y;
	loop invariant 0 <= x % (y + 1) || 0 <= x;
	loop invariant 0 <= x % (y + 1) || (y-1)*(y-1) <= x;
	loop invariant 0 < y;;
	loop invariant 0 < x;;
	loop invariant 0 < x % (y + 1);
	loop invariant (y-1)*(y-1) <= x;
	loop invariant (y-1)*(y-1) <= x || y <= x;
	loop invariant (y-1)*(y-1) <= x || 1 <= x;
	loop invariant (y-1)*(y-1) <= x || 0 <= y;
	loop invariant (y-1)*(y-1) <= x || 0 <= x;
	loop invariant (y-1)*(y-1) < x;
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
