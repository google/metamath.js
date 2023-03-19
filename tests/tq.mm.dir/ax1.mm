
axiom ax1
  param wx: wff x
  param wy: wff y
  param wz: wff z
  assume ax1.1: |- x t y q z
  assert |- x t y - q z x
end
