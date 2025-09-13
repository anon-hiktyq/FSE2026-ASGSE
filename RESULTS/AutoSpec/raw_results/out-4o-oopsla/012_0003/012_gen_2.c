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
  loop invariant 0 <= a;
  loop invariant s == (a * (a + 1)) / 2;
  loop invariant t == b * (flag ? 2 : 1) + (flag ? s : 0);
  loop assigns a, b, s, t;
  
  loop invariant 1 <= x;
  loop invariant y <= x + 2;
  loop invariant y % 2 == (x % 2 == 0 ? 0 : 1);
  loop assigns y;
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

