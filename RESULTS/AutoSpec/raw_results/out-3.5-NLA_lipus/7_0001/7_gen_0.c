
/*@ requires x >= 1;
    requires y >= 1;
*/
void main7(int x,int y){
  
  int a,b,p,q,r,s;

  a = x;
  b = y;
  p = 1;
  q = 0;
  r = 0;
  s = 1;

 
  /*@
  Looking at this code, I need to generate loop invariants for the GCD-like algorithm with additional variables p, q, r, s that maintain certain relationships.
  
  ```c
  loop invariant a >= 1;
  loop invariant b >= 1;
  loop invariant a*p + b*q == x;
  loop invariant a*r + b*s == y;
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

  //@ assert(b == x*q + y*s);
}