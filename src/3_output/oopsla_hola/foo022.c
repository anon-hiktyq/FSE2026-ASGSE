
void foo022() {
  int x = 0;
  int y = 0;
  int z = 0;
  int k = 0;

  
            
        /*@
          loop invariant x >= 0;
          loop invariant y >= 0;
          loop invariant z >= 0;
          loop invariant x == y && y == z;
          loop invariant (k == 0 && z == 0 && y == 0 && x == 0) || (k == x + y + z);
          loop assigns x, y, z, k;
        */
            while(unknown())
  {
     if(k%3 == 0){
        x++;
     }
      
     y++;
     z++;
     k = x+y+z;
  }
            

  /*@ assert x == y && y == z ;*/
 
}
