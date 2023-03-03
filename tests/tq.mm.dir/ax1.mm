
axiom ax1
  let wx: wff x
  let wy: wff y
  let wz: wff z
  assume ax1.1: |- x t y q z
  assert |- x t y - q z x
end
