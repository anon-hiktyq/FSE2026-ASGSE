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
  Looking at this code, I need to generate loop invariants for the GCD-like algorithm that maintains the relationship between the variables throughout the loop execution.
  
  ```c
  loop invariant a >= 1 && b >= 1;
  loop invariant a*p + b*q == x;
  loop invariant a*r + b*s == y;
  loop invariant p*s - q*r == 1;
  loop assigns a, b, p, q, r, s;
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
 
  //@ assert((r-s) * y == (q-p) * x);
}