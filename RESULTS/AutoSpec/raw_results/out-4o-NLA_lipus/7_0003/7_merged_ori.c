
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
  loop invariant y == a*r + b*s;
  loop invariant y == a * r + b * s;
  loop invariant x*q + y*s == b;
  loop invariant x == a*p + b*q;
  loop invariant x == a * p + b * q;
  loop invariant x * s - y * r == b;
  loop invariant x * q - y * p == a;
  loop invariant s >= 0 || s == b;
  loop invariant r >= 0 || r == a;
  loop invariant q >= 0 || q == b;
  loop invariant p >= 0 || p == a;
  loop invariant b >= a ==> q >= p && s >= r;
  loop invariant b == x*q + y*s;
  loop invariant b == x * q + y * s;;
  loop invariant b == x * q + y * s;
  loop invariant a >= b || b >= a;
  loop invariant a >= b || b > a;
  loop invariant a >= b ==> p >= q && r >= s;
  loop invariant a >= 1 && b >= 1;
  loop invariant a == x*p + y*r;
  loop invariant a == x * p + y * r;;
  loop invariant a == x * p + y * r;
  loop invariant a == b || a != b;
  loop invariant 1 <= y;
  loop invariant 1 <= x;
  loop invariant 1 <= b;
  loop invariant 1 <= a;
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