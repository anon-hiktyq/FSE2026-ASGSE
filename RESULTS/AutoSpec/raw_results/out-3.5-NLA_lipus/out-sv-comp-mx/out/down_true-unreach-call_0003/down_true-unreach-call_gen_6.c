#include "assert.h"

/*@
requires 0 < n;
*/
int foo(int n) {
	int k = 0;
	int i = 0;

	/*@
	loop invariant 0 <= i <= n;
	loop invariant k == i;
	loop assigns i, k;
	*/
	while (i < n) {
		i++;
		k++;
	}
	int j = n;
	while (j > 0) {
		// @ assert k > 0;
		j--;
		k--;
	}

	return 0;
}