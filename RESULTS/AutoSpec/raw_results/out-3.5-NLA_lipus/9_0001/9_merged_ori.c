/*@
requires z>=0 && z<=10 && k>0 && k<=10;
*/

void main9(int z,int k){
  

  int x=1;
  int y=z;
  int c=1;

  /*@
  loop invariant x*z - x - y + 1 == 0;
  loop invariant c <= k;
  loop invariant 1 <= x;
  loop invariant 1 <= c;
  loop invariant 0 <= y;
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
