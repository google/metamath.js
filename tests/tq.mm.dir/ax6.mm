
axiom ax6(wx: wff x, wz: wff z) {
  assume ax6.1: |- "z DF x";
  assume ax6.2: |- "x - DND z";

  return |- "z DF x -";
}
