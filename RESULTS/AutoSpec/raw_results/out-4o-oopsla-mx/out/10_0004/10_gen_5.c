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
  loop invariant x == y;
  loop invariant w == 1 || w == 0;
  loop invariant z == 1 || z == 0;
  loop invariant (w == 0 ==> x > y);
  loop invariant (z == 0 ==> y > x);
  loop assigns x;
  loop assigns y;
  loop assigns w;
  loop assigns z;
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
