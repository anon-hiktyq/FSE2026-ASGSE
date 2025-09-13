#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

void main()
{
  int x = 0;
  int y = 0;
  int i = 0;
  int j = 0;

  while(unknown1())
  {
    /*@
    loop invariant i >= 0 && j >= 0;
    loop invariant x >= y;
    loop invariant \forall integer k; 0 <= k < i ==> x == y;
    loop invariant \forall integer k; 0 <= k < j ==> x != y;
    loop assigns i, j, x, y;
    */
    while(unknown2())
    {
       if(x == y)
          i++;
       else
          j++;
    }
    if(i >= j)
    {
       x++;
       y++;
    }
    else
       y++;
  }

  // @ assert i >= j;
}
