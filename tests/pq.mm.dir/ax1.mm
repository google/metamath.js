
axiom ax1
  param wx: wff x
  param wy: wff y
  param wz: wff z
  assume ax1.1: |- x p y q z
  assert |- x p y - q z -
end
