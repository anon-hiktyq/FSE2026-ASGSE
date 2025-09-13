/*@ requires x >= 1;
    requires y >= 1;
*/
void main8(int x,int y){
  
  int a,b,p,q,r,s;
 
  a = x;
  b = y;
  p = 1;
  q = 0;
  r = 0;
  s = 1;

 
  /*@
  loop invariant p * s - q * r == 1;
  loop invariant a * s - b * r == y;
  loop invariant a * q - b * p == -x;
  loop invariant 1 <= b;
  loop invariant 1 <= a;
  loop assigns s;
  loop assigns r;
  loop assigns q;
  loop assigns p;
  loop assigns b;
  loop assigns a;
  ```c;
  ```;
  Looking at this code, I need to generate loop invariants that maintain the mathematical relationships throughout the GCD-like algorithm.;
  */
  while(a!=b){
      if (a>b) {
         a = a-b;
         p = p-q;
         r = r-s;
      }
      else {
         b = b-a;
         q = q-p;
         s = s-r;
      }
  }
 
  //@ assert((r-s) * y == (q-p) * x);
}