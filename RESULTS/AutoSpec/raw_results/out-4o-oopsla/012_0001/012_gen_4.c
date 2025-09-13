int unknown1();
int unknown2();


int foo012(int flag)
{
  int t = 0;
  int s = 0;
  int a = 0;
  int b = 0;

  /*@
  ```c
  loop invariant a == b;
  loop invariant t >= s;
  loop invariant t == 2*s - a || t == 2*s;
  loop invariant t - s <= a;
  loop assigns a, b, s, t;
  
  loop invariant 0 <= y <= x + 2;
  loop invariant y % 2 <= 1;
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

