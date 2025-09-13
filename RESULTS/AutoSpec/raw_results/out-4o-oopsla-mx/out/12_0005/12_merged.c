int unknown1();
int unknown2();


int main(int flag)
{
  int t = 0;
  int s = 0;
  int a = 0;
  int b = 0;
  /*@
  loop invariant t == b*(b+1)/2 + (flag ? a*(a+1)/2 : 0);
  loop invariant t == b * (b + 1) / 2 + (flag ? a * (a + 1) / 2 : 0);
  loop invariant t <= 2*s;
  loop invariant t <= 2 * s;
  loop invariant s == a*(a+1)/2;
  loop invariant s == a * (a + 1) / 2;
  loop invariant s == (a * (a + 1)) / 2;
  loop invariant s <= t;
  loop invariant flag ==> t >= 2 * s;
  loop invariant a == b;
  loop invariant 0 <= b;
  loop invariant 0 <= a;
  loop invariant 0 <= a == b;
  loop invariant 0 <= a && 0 <= b;
  loop assigns t;
  loop assigns s;
  loop assigns flag;
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
  //2s >= t
  int x = 1;
  if(flag) {
    x = t - 2*s + 2;
  }
  //x <= 2
  int y = 0;
  while(y <= x){
    if(unknown2()) 
       y++;
    else 
       y += 2;
  }
  // @ assert y <= 4;
}

