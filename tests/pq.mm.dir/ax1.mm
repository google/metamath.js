include "lexicon.mm"

axiom ax1
  let wff x
  let wff y
  let wff z
  assume ax1.1: |- x p y q z
  assert |- x p y - q z -
end
