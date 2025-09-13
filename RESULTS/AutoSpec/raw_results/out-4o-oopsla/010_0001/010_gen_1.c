
int unknown();


void foo010() {


  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;


  /*@
  loop invariant x == y;
  loop invariant 0 <= x;
  loop invariant 0 <= y;
  loop invariant w == 0 || w == 1;
  loop invariant z == 0 || z == 1;
  loop assigns x;
  loop assigns y;
  loop assigns w;
  loop assigns z;
  */
  while(unknown()){
  	if(w) {
  	  x++;
  	  w = !w;
	  }
	
    if(!z) {
      y++; 
      z=!z;
    }
  }

  // @ assert x == y;
  
}
