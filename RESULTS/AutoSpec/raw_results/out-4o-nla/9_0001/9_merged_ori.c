/*@
requires z>=0 && z<=10 && k>0 && k<=10;
*/

int main9(int z,int k){
  

  int x=1;
  int y=z;
  int c=1;

  /*@
  loop invariant z >= 0 && z <= 10;
  loop invariant y == z^c; // y is z raised to the power of c;
  loop invariant y == z^c;
  loop invariant x*z - x - y + 1 == 0;
  loop invariant x == z^c + z^(c-1) + ... + z + 1;
  loop invariant x == z^(c-1) + z^(c-2) + ... + z^0;
  loop invariant x == (z^c - 1) / (z - 1);
  loop invariant x == (z^(c-1)) + (z^(c-2)) + ... + z + 1; // Summation representation for x;
  loop invariant x == (z^(c-1) + z^(c-2) + ... + z^0);
  loop invariant x * z - x - y + 1 == 0; // Ensures the relationship between x and y holds;
  loop invariant x * z - x - y + 1 == 0;
  loop invariant k > 0 && k <= 10;
  loop invariant c <= k;
  loop invariant 1 <= c;
  loop invariant 0 < c;
  loop assigns y;
  loop assigns x;
  loop assigns c;
  */
  while (c < k){
 c = c + 1;
 x = x*z + 1;
 y = y*z;
  }

// @ assert x*z - x - y + 1 == 0;
}
