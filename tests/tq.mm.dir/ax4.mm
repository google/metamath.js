
axiom ax4(wx: wff x, wy: wff y) {
  assume ax4.1: |- "x DND y";

  return '|-' "x DND x y";
}
