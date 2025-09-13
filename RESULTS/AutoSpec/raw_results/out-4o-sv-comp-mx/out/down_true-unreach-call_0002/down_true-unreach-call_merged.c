#include "assert.h"

/*@
requires 0 < n;
*/
int foo(int n) {
	int k = 0;
	int i = 0;

	/*@
	loop invariant k == i;
	loop invariant i <= n;
	loop invariant 0 <= i;
	loop assigns k;
	loop assigns i;
	*/
	while (i < n) {
		i++;
		k++;
	}
	int j = n;
	/*@
	loop invariant k == j;
	loop invariant j <= n;
	loop invariant 0 <= k;
	loop invariant 0 <= j;
	loop assigns k;
	loop assigns j;
	*/
	while (j > 0) {
		//@ assert k > 0;
		j--;
		k--;
	}

	return 0;
}