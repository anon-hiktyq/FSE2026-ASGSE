/*@ requires x >= 1;
    requires y >= 1;
*/
void main5(int x,int y){
  
  int a,b,p,q,r,s;
 
  a = x;
  b = y;
  p = 1;
  q = 0;
  r = 0;
  s = 1;

 
  /*@
  loop invariant p*s - r*q == 1;
  loop invariant a*s + b*r == x;
  loop invariant a*q + b*p == y;
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
  The loop implements the extended Euclidean algorithm, and I need to identify what remains invariant. Key observations:;
  Looking at this code, I need to analyze the loop structure and what properties are maintained throughout execution.;
  - The variables p, q, r, s form a 2x2 matrix with determinant 1;
  - The matrix equation [a b] = [x y] * [p q; r s] holds;
  - The loop terminates when a == b;
  - The GCD relationships are preserved;
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
 
  //@ assert(1 == p*s - r*q);
}
