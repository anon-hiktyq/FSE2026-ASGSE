
void foo036(int flag) {
  int a = 0;
  int b = 0;
  int x = 0;
  int y = 0;
  int z = 0;
  int j = 0;
  int w = 0;

 
  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              loop assigns w, z, x, y, a, b;
            */
            while (unknown1()) {
    int i = z;
    int j = w;
    int k = 0;
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              loop invariant i >= z && j >= w && k >= 0;
            */
            while (i < j) {
      k++;
      i++;
    }
            

    x = z;
    y = k;

    if (x % 2 == 1) {
      x++;
      y--;
    }

  
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              loop invariant (x >= 0 && y >= 0) ==> (x + y >= 0);
            */
            while (unknown2()) {
      if (x % 2 == 0) {
        x += 2;
        y -= 2;
      } else {
        x--;
        y--;
      }
    }
            
    z++;
    w = x + y + 1;
  }
            


  int c = 0;
  int d = 0;
  
  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              loop assigns c, d, a, b;
            */
            while (unknown3()) {
    c++;
    d++;
    if (flag) {
      a++;
      b++;
    } else {
      a += c;
      b += d;
    }
  }
            
  /*@ assert w >= z && a - b == 0;*/
}
