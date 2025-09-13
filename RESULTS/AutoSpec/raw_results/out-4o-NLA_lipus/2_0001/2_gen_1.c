/*@ requires x>0;
    requires y>0;
*/
void main2(int x,int y){
 
  int q=0;
  int r=0;
  
  /*@
  loop invariant x > y * q + r - y;
  loop invariant 0 <= r < y;
  loop invariant q >= 0;
  loop invariant y * q + r == \old(y) * q + \sum(0, q, i, y - 1) + r;
  loop assigns q, r;
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
