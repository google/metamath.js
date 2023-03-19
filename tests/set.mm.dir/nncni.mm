include "nnrei.mm"
include "recni.mm"

theorem nncni
  let cA: class A
  assume nnre.1: |- A e. NN


  assert |- A e. CC

  proof
    cA
    cA
    nnre.1
    nnrei
    recni
end
