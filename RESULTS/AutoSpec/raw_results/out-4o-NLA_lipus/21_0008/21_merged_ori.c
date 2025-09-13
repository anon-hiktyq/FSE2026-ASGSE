int unknown();
void main21(){
	int x = 0;
	int y = 0;

	/*@
	loop invariant y*y <= 2*x;
	loop invariant y*y <= 2*x || x <= y * y + 2*y;
	loop invariant y*y <= 2*x || 0 <= y;
	loop invariant y*y < 2*x;
	loop invariant y * y == x;
	loop invariant y * y <= x;
	loop invariant y * y <= x || y*y <= 2*x;
	loop invariant y * y <= x || x <= y * y + 2*y;
	loop invariant y * y <= x || 0 <= y;
	loop invariant y * y <= x || (y * (y - 1)) + y <= x;
	loop invariant y * y < x;
	loop invariant x == y * (y - 1) + y;
	loop invariant x <= y * y + 2*y;
	loop invariant x <= y * y + 2*y || 0 <= y;
	loop invariant x <= (y + 1) * (y + 1);
	loop invariant x <= (y + 1) * (y + 1) || y*y <= 2*x;
	loop invariant x <= (y + 1) * (y + 1) || y * y <= x;
	loop invariant x <= (y + 1) * (y + 1) || x <= y * y + 2*y;
	loop invariant x <= (y + 1) * (y + 1) || 0 <= y;
	loop invariant x <= (y + 1) * (y + 1) || (y * (y - 1)) + y <= x;
	loop invariant x < y * y + 2*y;
	loop invariant x < (y + 1) * (y + 1);
	loop invariant \forall integer k; 0 <= k <= y ==> x >= k * k;;
	loop invariant 0 <= y;;
	loop invariant 0 < y;;
	loop invariant 0 < y;;
	loop invariant 0 < y;;
	loop invariant 0 < y;;
	loop invariant 0 < y;;
	loop invariant 0 < y;;
	loop invariant 0 < y;;
	loop invariant 0 < y;;
	loop invariant 0 < y;;
	loop invariant 0 < y;;
	loop invariant (y * (y - 1)) + y <= x;
	loop invariant (y * (y - 1)) + y <= x || y*y <= 2*x;
	loop invariant (y * (y - 1)) + y <= x || x <= y * y + 2*y;
	loop invariant (y * (y - 1)) + y <= x || 0 <= y;
	loop invariant (y * (y - 1)) + y < x;
	loop invariant y <= x;
	loop invariant x == y * y;
	loop invariant x == (y * (y - 1)) + y;
	loop invariant x == (y * (y + 1)) - y;
	loop invariant \forall integer k; 0 <= k <= y ==> x >= k * k;
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
