
/*@ requires x >= 1;
    requires y >= 1;
*/
int main7(int x,int y){
  
  int a,b,p,q,r,s;

  a = x;
  b = y;
  p = 1;
  q = 0;
  r = 0;
  s = 1;

 
  /*@
  loop invariant y == a*r + b*s;
  loop invariant x == a*p + b*q;
  loop invariant r*x + s*y == b;
  loop invariant p*x + q*y == a;
  loop invariant b == x*q + y*s;
  loop invariant b == x * q + y * s;
  loop invariant a >= 1 && b >= 1;
  loop invariant a >= 0 && b >= 0;
  loop invariant a == x*p + y*r;
  loop invariant a == x * p + y * r;
  loop invariant a == b ==> x*p + y*r == x*q + y*s;
  loop invariant a != b ==> p*s - q*r == 1;
  loop invariant a != b ==> p*r + q*s == 1;
  loop invariant a != b ==> (a >= 1 && b >= 1);
  loop invariant \exists integer k; a == k * b && b == k * a;
  loop invariant 1 <= b;
  loop invariant 1 <= a;
  loop invariant 0 < \abs(r) + \abs(s);
  loop invariant 0 < \abs(p) + \abs(q);
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