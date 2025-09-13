
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
  Looking at this code, I need to generate loop invariants for the GCD-like algorithm that maintains the relationship between the variables.
  
  ```c
  loop invariant a > 0;
  loop invariant b > 0;
  loop invariant x*p + y*r == a;
  loop invariant x*q + y*s == b;
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