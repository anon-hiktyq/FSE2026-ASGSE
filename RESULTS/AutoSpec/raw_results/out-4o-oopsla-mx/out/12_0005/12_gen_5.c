int unknown1();
int unknown2();


int main(int flag)
{
  int t = 0;
  int s = 0;
  int a = 0;
  int b = 0;
  /*@
  loop invariant a == b;
  loop invariant s == \sum(1, a);
  loop invariant t == \sum(1, b) + (\sum(1, a) * flag);
  loop invariant 2*s >= t;
  loop assigns a;
  loop assigns b;
  loop assigns s;
  loop assigns t;
  loop assigns flag;
  
  loop invariant 0 <= y <= x;
  loop invariant x <= 2;
  loop invariant x == t - 2*s + 2 || x == 1;
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

