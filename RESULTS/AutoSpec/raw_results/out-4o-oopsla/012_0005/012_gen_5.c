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
  loop invariant t == s + (flag ? a : 0);
  loop invariant t >= s;
  loop invariant s >= 0;
  loop invariant t >= 0;
  loop assigns a, b, s, t;
  
  loop invariant y >= 0;
  loop invariant y <= x + 2;
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

