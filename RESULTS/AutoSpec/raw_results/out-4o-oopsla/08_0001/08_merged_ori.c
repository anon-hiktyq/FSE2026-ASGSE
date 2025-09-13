int unknown1();
int unknown2();
int unknown3();


void foo08() {
 int x = 0, y = 0;

 /*@
 loop invariant y >= 100 * x || x <= 0;
 loop invariant y == 100 * (x - \old(x)) + \old(y) || (x >= 4 && y == (x - 4 + \old(y))) || (x < 0 && y == \old(y) - 1);
 loop invariant y <= 100 * x;
 loop invariant x < 4 || y > 2;
 loop invariant 0 <= y;
 loop invariant 0 <= x;
 loop invariant (x >= 4) ==> y >= 0;
 loop invariant (x >= 4 ==> y >= x * 100) || y < 100;
 loop invariant (x >= 4 && \exists integer k; 0 <= k <= x-4 && y > 2 + k);
 loop invariant (x < 4) || (y > 2);
 loop invariant (x < 0 ==> y < 0) || y >= 0;
 loop assigns y;
 loop assigns x;
 */
 while(unknown1()) {
   if(unknown2()) { 
      x++; 
      y += 100; 
   }
   else if (unknown3()){ 
      if (x >= 4) { 
          x++; 
          y++; 
      } 
      if (x < 0) {
          y--;
      }
   }
  
 }
 // @ assert x < 4 || y > 2;
}
