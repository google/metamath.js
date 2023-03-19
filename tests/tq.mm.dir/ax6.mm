
axiom ax6
  param wx: wff x
  param wz: wff z
  assume ax6.1: |- z DF x
  assume ax6.2: |- x - DND z
  assert |- z DF x -
end
