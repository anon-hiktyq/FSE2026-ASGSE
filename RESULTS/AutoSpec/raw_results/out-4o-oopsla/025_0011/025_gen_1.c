
int unknown1();
int unknown2();


void foo025() {
  int x = 0;
  int y = 0;
  int i = 0;
  int j = 0;

 
  while(unknown1())
  {
    
    /*@
    loop invariant i >= 0 && j >= 0;
    loop invariant x >= y;
    loop invariant \forall integer k; x == y ==> (i >= j);
    loop assigns i, j, x, y;
    */
    while(unknown2())
    {
       if(x == y){
          i++;
       }else{
          j++;
       }
    }

    if(i >= j)
    {
       x++;
       y++;
    }
    else{
       y++;
    }
  }

  // @ assert i >= j;
}
