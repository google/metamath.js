
axiom ax1(wx: wff x, wy: wff y, wz: wff z) {
  assume ax1.1: |- "x p y q z";

  return |- "x p y - q z -";
}
