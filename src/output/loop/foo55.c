
void foo55(int flag)
{
    int x = 0;
    int y = 0;
    int j = 0;
    int i = 0;

    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant x == y;
      loop invariant i == x * (x + 1) / 2;
      loop invariant j >= i;
      loop invariant flag == \at(flag, Pre);
      loop assigns x, y, i, j;
    */
    while(unknown())
    {
        x++;
        y++;
        i += x;
        j += y;
        if (flag){
            j += 1;
        }
    }
    
    /*@ assert j >= i; */
}
