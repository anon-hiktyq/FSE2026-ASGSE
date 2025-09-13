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
  Looking at this code, I need to analyze the loop structure and what properties are maintained throughout execution.
  
  The loop implements the extended Euclidean algorithm, and I need to identify what remains invariant. Key observations:
  - The loop terminates when a == b
  - The variables p, q, r, s form a 2x2 matrix with determinant 1
  - The GCD relationships are preserved
  - The matrix equation [a b] = [x y] * [p q; r s] holds
  
  ```c
  loop invariant a >= 1;
  loop invariant b >= 1;
  loop invariant p*s - r*q == 1;
  loop invariant a*s + b*r == x;
  loop invariant a*q + b*p == y;
  loop assigns a;
  loop assigns b;
  loop assigns p;
  loop assigns q;
  loop assigns r;
  loop assigns s;
  ```
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
