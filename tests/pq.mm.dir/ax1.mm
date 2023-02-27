include "lexicon.mm"

axiom ax1
  let wx: wff x
  let wy: wff y
  let wz: wff z
  assume ax1.1: |- x p y q z
  assert |- x p y - q z -
end
