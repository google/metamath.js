include "cn0.mm"
include "cz.mm"
include "nn0ssz.mm"
include "sselii.mm"

theorem nn0zi
  let cN: class N
  assume nn0zi.1: |- N e. NN0


  assert |- N e. ZZ

  proof
    cn0
    cz
    cN
    nn0ssz
    nn0zi.1
    sselii
end
