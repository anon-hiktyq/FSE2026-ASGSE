int unknown1();
int unknown2();


int main(int flag)
{
  int t = 0;
  int s = 0;
  int a = 0;
  int b = 0;
  /*@
  loop invariant 0 <= a;
  loop invariant 0 <= b;
  loop invariant s == (a * (a + 1)) / 2;
  loop invariant t == (b * (b + 1)) / 2;
  loop invariant \forall integer k; 0 <= k < a ==> 2*s >= t;
  loop assigns a;
  loop assigns b;
  loop assigns s;
  loop assigns t;
  
  loop invariant 0 <= y <= x+1;
  loop invariant x <= 2;
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

