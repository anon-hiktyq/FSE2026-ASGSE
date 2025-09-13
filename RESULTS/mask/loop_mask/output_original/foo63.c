
void foo63()
{
  int x = 0;
  int y = 0;
  int i = 0;
  int j = 0;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
    loop invariant x >= 0;
    loop invariant y >= 0;
    loop invariant i >= 0;
    loop invariant j >= 0;
  */
  while(unknown1())
  {
    /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
      loop invariant x >= 0;
      loop invariant y >= 0;
      loop invariant i >= 0;
      loop invariant j >= 0;
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

  /* mask_1 */
}
