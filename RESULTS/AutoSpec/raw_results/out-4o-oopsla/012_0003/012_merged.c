int unknown1();
int unknown2();


int foo012(int flag)
{
  int t = 0;
  int s = 0;
  int a = 0;
  int b = 0;

  /*@
  loop invariant t == s + (flag ? a : 0);
  loop invariant t == b * (flag ? 2 : 1) + (flag ? s : 0);
  loop invariant t == b * (flag ? 2 : 1) + (a * (a + 1)) / 2;
  loop invariant t == b * (b + 1) / 2;
  loop invariant t == b * (b + 1) / 2 || (flag && t == b * (b + 3) / 2);
  loop invariant t == b * (b + 1) / 2 + (flag ? b * (b + 1) / 2 : 0);
  loop invariant t == b * (b + 1) / 2 + (flag ? a * (a + 1) / 2 : 0);
  loop invariant s == b * (b + 1) / 2;
  loop invariant s == a*(a+1)/2;
  loop invariant s == a * (a + 1) / 2;
  loop invariant s == (a * (a + 1)) / 2;
  loop invariant s <= t;
  loop invariant flag == 0 ==> t == b;
  loop invariant flag != 0 ==> t == b + a * (a + 1) / 2;
  loop invariant a == b;
  loop invariant 0 <= b;
  loop invariant 0 <= a;
  loop invariant (t == s && !flag) || (t == 2*s && flag);
  loop assigns t;
  loop assigns s;
  loop assigns b;
  loop assigns a;
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

