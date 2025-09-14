
void foo57() {
 int x = 0, y = 0;

 /*@
   loop invariant x >= 0;
   loop invariant y >= 0;
   loop invariant x < 4 || y > 2;
   loop assigns x, y;
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
            
 /*@ assert x < 4 || y > 2; */
}
