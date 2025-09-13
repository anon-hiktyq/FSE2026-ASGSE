//terminator_03_true-unreach-call_true-termination.c

/*@
requires y <= 1000000;
*/
int foo(int x, int y) {
	//int x;
	//int y;

	if (y > 0) {
		/*@
		loop invariant y <= 1000000;
		loop invariant x == \old(x) + (\old(y) * (\count));
		loop invariant x <= 100 + (y * ((100 - x) / y));
		loop invariant x < 100;
		loop invariant x < 100 || x >= 100;
		loop invariant \old(x) <= x;
		loop invariant \exists integer k; x == k * y && k >= 0;
		loop invariant \exists integer k; k >= 0 && x == \old(x) + k * y;
		loop invariant \exists integer k; 0 <= k && x == k * y + \old(x);
		loop invariant 0 <= x;
		loop invariant 0 < y;
		loop assigns x;
		*/
		while (x < 100) {
			x = x + y;
		}
	}
	
	// @ assert y <= 0 || (y > 0 && x >= 100);

	return 0;
}
