
axiom ax4
  param wx: wff x
  param wy: wff y
  assume ax4.1: |- x DND y
  assert |- x DND x y
end
