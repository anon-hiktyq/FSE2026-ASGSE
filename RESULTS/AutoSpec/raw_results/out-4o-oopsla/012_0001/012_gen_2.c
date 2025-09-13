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
  loop invariant t == b * (1 + (flag ? 1 : 0));
  loop invariant s == a * (a + 1) / 2;
  loop invariant t >= s;
  loop invariant t % 2 == (flag ? 0 : t % 2);
  loop invariant 0 <= a;
  loop assigns a, b, t, s;
  
  loop invariant 0 <= y <= x + 2;
  loop invariant y % 2 == x % 2;
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

