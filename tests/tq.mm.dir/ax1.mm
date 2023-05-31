
axiom ax1(wx: $wff$ x, wy: $wff$ y, wz: $wff$ z) {
  assume ax1.1: $|- x t y q z$;

  return $|-$ $x t y - q z x$;
}
