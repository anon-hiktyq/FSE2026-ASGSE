int unknown1();
int unknown2();


int main(int flag)
{
  int t = 0;
  int s = 0;
  int a = 0;
  int b = 0;
  /*@
  loop invariant y <= x+1;
  loop invariant y <= x + 2;
  loop invariant y <= x + 1;
  loop invariant y <= flag * 2 + 2;
  loop invariant y <= 4;
  loop invariant y % 2 == 0 ==> y <= x;
  loop invariant x <= 2;
  loop invariant t == s + a*(flag ? 1 + a : 1);
  loop invariant t == b*(b+1)/2 + (flag ? a*(a+1)/2 : 0);
  loop invariant t == b * (b + 1) / 2 + (flag ? s : 0);
  loop invariant t == b * (2 - flag) + flag * a;
  loop invariant t == b * (1 + flag) + (b * (b - 1)) / 2;
  loop invariant t == (b * (b + 1)) / 2;
  loop invariant t <= 2*s;
  loop invariant t <= 2 * s;
  loop invariant s == a*(a+1)/2;
  loop invariant s == a * (a + 1) / 2;
  loop invariant s == a * (1 + flag) / 2;
  loop invariant s == (a * (a + 1)) / 2;
  loop invariant s <= t;
  loop invariant b <= t;
  loop invariant a == b;
  loop invariant a <= s;
  loop invariant \forall integer k; 0 <= k < a ==> 2*s >= t;
  loop invariant 0 <= y;
  loop invariant 0 <= t;
  loop invariant 0 <= s;
  loop invariant 0 <= b;
  loop invariant 0 <= a;
  loop assigns y;
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

