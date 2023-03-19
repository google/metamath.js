include "nn0rei.mm"
include "recni.mm"

theorem nn0cni
  let cA: class A
  assume nn0rei.1: |- A e. NN0


  assert |- A e. CC

  proof
    cA
    cA
    nn0rei.1
    nn0rei
    recni
end
