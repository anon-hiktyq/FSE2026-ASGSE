int unknown1();
int unknown2();


int foo012(int flag)
{
  int t = 0;
  int s = 0;
  int a = 0;
  int b = 0;

  /*@
  loop invariant y <= x;
  loop invariant y <= x+1;
  loop invariant y <= x + 2;
  loop invariant t == s + b;
  loop invariant t == b*(b+1)/2;
  loop invariant t == b*(b+1)/2 + (flag ? a*(a+1)/2 : 0);
  loop invariant t == b * (flag ? 2 : 1);
  loop invariant t == b * (b + 1) / 2;
  loop invariant t == b * (b + 1) / 2 + (flag ? a * a : 0);
  loop invariant t == b * (1 + \at(flag, Pre));
  loop invariant t == (b * (b + 1)) / 2 + (flag ? a * a : 0);
  loop invariant s == a;
  loop invariant s == a*(a+1)/2;
  loop invariant s == a * (a + 1) / 2;
  loop invariant s == (a*(a+1))/2;
  loop invariant s == (a * (a + 1)) / 2; // Sum of first a natural numbers;
  loop invariant s == (a * (a + 1)) / 2;
  loop invariant s <= t;
  loop invariant flag ==> x == t - 2*s + 2;
  loop invariant flag ==> t >= 2 * s;
  loop invariant flag ==> t == s + a*b;
  loop invariant flag ==> t == s + a * a;
  loop invariant flag ==> t == 2*s + a;
  loop invariant a == b;
  loop invariant \at(flag, Pre) ==> t == s + a;
  loop invariant 0 <= y;
  loop invariant 0 <= b;
  loop invariant 0 <= a;
  loop invariant 0 <= a == b;
  loop invariant !flag ==> t == s;
  loop invariant !\at(flag, Pre) ==> t == b;
  loop assigns y;
  loop assigns t;
  loop assigns s;;
  loop assigns s;
  loop assigns b;;
  loop assigns b;
  loop assigns a;;
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

