int main() {
  int x = 0;
  
  /*@
  loop invariant 0 <= x <= 100;
  loop invariant x == \at(x, Pre) + \at(\num_of_iterations, Pre);
  loop assigns x;
  */
  while (x < 100) {
    x = x + 1;
  }
  // post-condition
  // @ assert x == 100;
}