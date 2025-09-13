int unknown1();
int unknown2();


int main(int flag)
{
  int t = 0;
  int s = 0;
  int a = 0;
  int b = 0;
  /*@
  loop invariant y <= x + 2;
  loop invariant x <= 2;
  loop invariant t == s + b * (flag ? 1 : 0);
  loop invariant t == b * b + (flag ? a * (a + 1) / 2 : 0);
  loop invariant t == b * (flag ? 2 : 1);
  loop invariant t == b * (flag ? 2 : 1) + s;
  loop invariant t == b * (flag ? (b + 1) : 1);
  loop invariant t == b * (b + 1) / 2 + (flag ? a * a : 0);
  loop invariant t == b * (b + 1) / 2 + (flag ? a * (a + 1) / 2 : 0);
  loop invariant t == b * (b + 1) / 2 + (flag ? (a * (a + 1)) / 2 : 0);
  loop invariant t == b * (1 + flag) + (flag ? (a * (a + 1)) / 2 : 0);
  loop invariant t <= 2 * s;
  loop invariant s == a * (a + 1) / 2;
  loop invariant s == (a * (a + 1)) / 2; // Sum of first `a` integers;
  loop invariant s == (a * (a + 1)) / 2;
  loop invariant s <= t;
  loop invariant a == b;
  loop invariant 2 * s <= t;
  loop invariant 1 <= x;
  loop invariant 0 <= y;
  loop invariant 0 <= t;
  loop invariant 0 <= s;
  loop invariant 0 <= a && 0 <= b;
  loop assigns y;
  loop assigns t;
  loop assigns s;
  loop assigns b;
  loop assigns a;
  ```c;
  ```;
  For the second loop:;
  For the first loop:;
  /* Loop Invariants for the second loop */;
  /* Loop Invariants for the first loop */;
  /* Infill for the second while loop */;
  /* Infill for the first while loop */;
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

