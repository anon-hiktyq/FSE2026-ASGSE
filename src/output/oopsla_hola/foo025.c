



void foo025() 
{
  int x = 0;
  int y = 0;
  int i = 0;
  int j = 0;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
    loop invariant x == y;
    loop invariant i >= j;
  */
  while(unknown1())
  {
    /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
      loop invariant i >= j;
      loop invariant x == y;
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

  /*@ assert i >= j; */
}