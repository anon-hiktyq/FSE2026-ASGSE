int unknown1();
int unknown2();


int main(int flag)
{
  int t = 0;
  int s = 0;
  int a = 0;
  int b = 0;
  /*@
  For the first loop:
  ```c
  loop invariant a == b;
  loop invariant s == (a * (a + 1)) / 2;
  loop invariant t == (b * (b + 1)) / 2 + (flag ? s : 0);
  loop invariant t >= 2 * s;
  loop invariant a >= 0;
  loop invariant b >= 0;
  loop assigns a, b, s, t;
  ```
  
  For the second loop:
  ```c
  loop invariant 0 <= y <= x + 1;
  loop invariant x <= 2;
  loop assigns y;
  ```
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

