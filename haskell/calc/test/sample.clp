Overall we got {animals:C4} animals.

DATA animals {
  type:string,legs:natural,number:natural;
  dog,4,1;
  cat,4,3;
  shark,0,10;
  total:natural,{sum(B1:B3)},{sum(C1:C3)};
}
