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
  loop invariant t >= s;
  loop invariant flag ==> t == 2*a + s;
  loop invariant !flag ==> t == a + s;
  loop invariant 0 <= a;
  loop invariant 0 <= b;
  loop invariant 0 <= t;
  loop invariant 0 <= s;
  loop assigns a;
  loop assigns b;
  loop assigns t;
  loop assigns s;
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

