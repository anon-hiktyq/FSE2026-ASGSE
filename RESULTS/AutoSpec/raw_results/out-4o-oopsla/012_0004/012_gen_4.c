int unknown1();
int unknown2();


int foo012(int flag)
{
  int t = 0;
  int s = 0;
  int a = 0;
  int b = 0;

  /*@
  loop invariant a == b;
  loop invariant s == (a * (a + 1)) / 2;
  loop invariant t == b * (1 + \at(flag, Pre));
  loop invariant \at(flag, Pre) ==> t == s + a;
  loop invariant !\at(flag, Pre) ==> t == b;
  loop assigns a;
  loop assigns b;
  loop assigns s;
  loop assigns t;
  */
  while(unknown1()) {
    a++;
    b++;
    s += a;
    t += b;
    if(flag) {
      t += a;
    }
  } 
 
  int x = 1;

  if(flag) {
    x = t - 2*s + 2;
  }
  
  int y = 0;
  
  while(y <= x){
    if(unknown2()) 
       y++;
    else 
       y += 2;
  }
  // @ assert y <= 4;
}

