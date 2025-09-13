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
	loop invariant j >= 0;
	loop invariant k == j;
	loop invariant k >= 0;
	loop assigns j;
	loop assigns k;
	*/
	while (j > 0) {
		// @ assert k > 0;
		j--;
		k--;
	}

	return 0;
}