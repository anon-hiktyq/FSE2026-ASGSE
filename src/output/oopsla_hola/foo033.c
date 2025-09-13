
void foo033(int k) {
  int z = k;
  int x = 0;
  int y = 0;

 
  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              loop invariant  (x >= y);
              loop invariant  (z == k + y);
              loop invariant  (x >= 0);
              loop invariant  (y >= 0);
              loop assigns x, y, z, c;
            */
            while(unknown1())
  {
    int c = 0;
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              c >= 0 && x >= 0 && y >= 0;
            */
            while(unknown2())
    {
      if(z==k+y-c)
      {
        x++;
        y++;
        c++;
      }else
      {
        x++;
        y--;
        c++;
      }
    }
            

    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              (x >= y) && (z == k + y);
            */
            while(unknown3())
    {
      x--;
      y--;
    }
            
    z=k+y;
  }
            

  /*@ assert x==y; */
}
