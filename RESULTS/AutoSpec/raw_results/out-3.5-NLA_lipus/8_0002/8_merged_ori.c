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
  loop invariant r*x + s*y == b;
  loop invariant p*x + q*y == a;
  loop invariant p*s - q*r == 1;
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
  Looking at this GCD-like algorithm, I need to analyze the invariants that hold throughout the loop execution.;
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