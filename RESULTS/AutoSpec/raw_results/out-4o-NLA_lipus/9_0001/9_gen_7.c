/*@
requires z>=0 && z<=10 && k>0 && k<=10;
*/

void main9(int z,int k){
  

  int x=1;
  int y=z;
  int c=1;

  /*@
  loop invariant 1 <= c <= k;
  loop invariant x == z*c + 1 - z;
  loop invariant y == z^c; 
  loop invariant c > 0;
  loop assigns x;
  loop assigns y;
  loop assigns c;
  */
  while (c < k){
 c = c + 1;
 x = x*z + 1;
 y = y*z;
  }

// @ assert x*z - x - y + 1 == 0;
}
