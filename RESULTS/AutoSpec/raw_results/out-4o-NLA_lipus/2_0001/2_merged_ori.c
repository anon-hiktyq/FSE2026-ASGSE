/*@ requires x>0;
    requires y>0;
*/
void main2(int x,int y){
 
  int q=0;
  int r=0;
  
  /*@
  loop invariant y * q <= x;
  loop invariant y * q + r == \old(y) * q + \sum(0, q, i, y - 1) + r;
  loop invariant y * q + r <= x;
  loop invariant y * q + r < x;
  loop invariant y * q + r - y < x;
  loop invariant x > y * q + r ==> q == x / y - 1;
  loop invariant x == y * q + r || x > y * q + r;
  loop invariant x == y * q + r + (x - (y * q + r));
  loop invariant x == (y * q + r) + (x - (y * q + r));
  loop invariant r < y;
  loop invariant q <= x / y;
  loop invariant q * y + r <= x;
  loop invariant 0 <= r;
  loop invariant 0 <= q;
  loop invariant 0 <= q && 0 <= r < y;
  loop invariant 0 <= (y * q + r);
  loop invariant 0 < y;
  loop invariant 0 < x;
  loop invariant (y * q + r) < x;
  loop assigns r;
  loop assigns q;
  */
  while(x > y * q + r) {
      if (r == y - 1){
          r = 0;
          q += 1;
      }
      else{
          r += 1;
      }

  }
  
  // @ assert q == x / y;
  
}
