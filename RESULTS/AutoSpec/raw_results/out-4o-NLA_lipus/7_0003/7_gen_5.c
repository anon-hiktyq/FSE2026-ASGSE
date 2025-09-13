
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
  loop invariant a >= 1 && b >= 1;
  loop invariant a == x * p + y * r;
  loop invariant b == x * q + y * s;
  loop invariant a >= 0;
  loop invariant b >= 0;
  loop invariant p >= 0 || p == a;
  loop invariant q >= 0 || q == b;
  loop invariant r >= 0 || r == a;
  loop invariant s >= 0 || s == b;
  loop assigns a, b, p, q, r, s;
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