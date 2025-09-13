
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
  loop invariant x*q + y*s == b;
  loop invariant x*p + y*r == a;
  loop invariant r*a + s*b == y;
  loop invariant r >= 0 && s >= 0;
  loop invariant r <= 0;
  loop invariant q <= 0;
  loop invariant q * x + s * y == b;
  loop invariant q * a == s * b;
  loop invariant p*a + q*b == x;
  loop invariant p >= 0 && q >= 0;
  loop invariant p * x + r * y == a;
  loop invariant p * b == r * a;
  loop invariant b == x*q + y*s;
  loop invariant b == x * q + y * s;
  loop invariant a >= b || b >= a;
  loop invariant a >= 0 && b >= 0;;
  loop invariant a >= 0 && b >= 0;
  loop invariant a == x*p + y*r;
  loop invariant a == x * p + y * r;
  loop invariant a - b == x*p + y*r - (x*q + y*s);
  loop invariant a + b == x + y;
  loop invariant a + b <= x + y;
  loop invariant 1 <= b;
  loop invariant 1 <= a;
  loop invariant 0 <= s;
  loop invariant 0 <= r;
  loop invariant 0 <= q;
  loop invariant 0 <= p;
  loop invariant 0 <= b;
  loop invariant 0 <= a;
  loop assigns s;
  loop assigns r;
  loop assigns q;
  loop assigns p;
  loop assigns b;
  loop assigns a;
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