method Main(b: bool, div: int) returns (i: int) {
  print 1;
  print "A";
  print [1,2+3,4];
  if b {
    return 4 + if true then 1 / div else 3;
  } else {
    return 1 / div;
  }
}
