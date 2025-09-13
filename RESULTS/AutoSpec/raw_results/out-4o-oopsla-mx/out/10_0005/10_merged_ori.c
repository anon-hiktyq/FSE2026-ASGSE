#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

void main() {


  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;

  /*@
  loop invariant z == !(y % 2);
  loop invariant y <= x;
  loop invariant x == y;
  loop invariant x == y || x == y + 1;
  loop invariant x == y && w != z;
  loop invariant x <= y;
  loop invariant x + y <= 2 * (\old(x) + \old(y));
  loop invariant w == !(x % 2);
  loop invariant w + z == 1;
  loop invariant \forall integer k; 0 <= k < y ==> z == 0;
  loop invariant \forall integer k; 0 <= k < y ==> k == x;
  loop invariant \forall integer k; 0 <= k < y ==> (w != z);
  loop invariant \forall integer k; 0 <= k < x ==> w == 1;
  loop invariant \forall integer k; 0 <= k < x ==> (w != z);
  loop invariant 0 <= x == y;
  loop invariant (z == 1) ==> (w == 0);
  loop invariant (z == 0) ==> (w == 1);
  loop invariant (x + y) % 2 == 0;
  loop invariant (w == 1) ==> (z == 0);
  loop invariant (w == 1 ==> x == y) && (z == 0 ==> x == y);
  loop invariant (w == 0) ==> (z == 1);
  loop invariant z == 1 || z == 0;
  loop invariant z == 0 || z == 1;
  loop invariant w == 1 || w == 0;
  loop invariant w == 0 || w == 1;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant (z == 1) || (z == 0);
  loop invariant (z == 0 || z == 1);
  loop invariant (w == 1) || (w == 0);
  loop invariant (w == 0 || w == 1);
  loop assigns z;
  loop assigns y;
  loop assigns x;
  loop assigns w;
  */
  while(unknown2()){
  	if(w) {
  	  x++;
  	  w = !w;
	  }
	
    if(!z) {
      y++; 
      z=!z;
    }
  }

  // @ assert x==y;
  
}
