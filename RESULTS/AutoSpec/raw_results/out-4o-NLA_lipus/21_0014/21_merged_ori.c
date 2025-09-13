int unknown();
void main21(){
	int x = 0;
	int y = 0;

	/*@
	loop invariant y; <= x;
	loop invariant y; < x;
	loop invariant y == \sqrt(x);;
	loop invariant y <= x || x <= (y + 1) * (y + 1) - 1;
	loop invariant y * y <= x;
	loop invariant y * y <= x || y <= x;
	loop invariant y * y <= x || x <= (y + 1) * (y + 1) - 1;
	loop invariant y * y <= x || 0 <= x;
	loop invariant y * y < x;
	loop invariant x == y * y;;
	loop invariant x == (y * (y + 1) / 2) * 2;;
	loop invariant x <= (y + 1) * (y + 1) - 1;
	loop invariant x < (y + 1) * (y + 1) - 1;
	loop invariant x < (y + 1) * (y + 1) - 1;
	loop invariant x < (y + 1) * (y + 1) - 1;
	loop invariant x < (y + 1) * (y + 1) - 1;
	loop invariant x < (y + 1) * (y + 1) - 1;
	loop invariant x < (y + 1) * (y + 1) - 1;
	loop invariant x < (y + 1) * (y + 1) - 1;
	loop invariant x < (y + 1) * (y + 1) - 1;
	loop invariant x % y == 0 || y > 0;
	loop invariant x % y == 0 || y == 0;;
	loop invariant \forall integer k; x == k * k ==> y == k;
	loop invariant \forall integer k; k >= 0 ==> y == k ==> x == k * k;
	loop invariant \forall integer k; 0 <= k <= y ==> x >= k * k;
	loop invariant \forall integer k; 0 <= k < y ==> k * k <= x;;
	loop invariant \exists integer k; k >= 0 && x == k * k;;
	loop invariant \exists integer k; k >= 0 && x == k * k && k == y;
	loop invariant 0; <= y;
	loop invariant 0; <= x;
	loop invariant 0; < y;
	loop invariant 0; < x;
	loop invariant 0 <= y || y <= x;
	loop invariant 0 <= y || y * y <= x;
	loop invariant 0 <= y || x <= (y + 1) * (y + 1) - 1;
	loop invariant 0 <= y || 0 <= x;
	loop invariant 0 <= x || y <= x;
	loop invariant 0 <= x || x <= (y + 1) * (y + 1) - 1;
	loop invariant x == y * y;
	loop invariant x % y == 0 || y == 0;
	loop invariant \exists integer k; k >= 0 && x == k * k;
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
