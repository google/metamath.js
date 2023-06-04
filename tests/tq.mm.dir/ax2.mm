
axiom ax2(wx: wff x, wy: wff y, wz: wff z) {
  assume ax2.1: |- "x - t y - q z";

  return '|-' "C z";
}
