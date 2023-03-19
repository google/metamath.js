include "cn0.mm"
include "cr.mm"
include "nn0ssre.mm"
include "sselii.mm"

theorem nn0rei
  let cA: class A
  assume nn0rei.1: |- A e. NN0


  assert |- A e. RR

  proof
    cn0
    cr
    cA
    nn0ssre
    nn0rei.1
    sselii
end
