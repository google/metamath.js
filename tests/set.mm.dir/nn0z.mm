include "cn0.mm"
include "cz.mm"
include "nn0ssz.mm"
include "sseli.mm"

theorem nn0z
  let cN: class N


  assert |- ( N e. NN0 -> N e. ZZ )

  proof
    cn0
    cz
    cN
    nn0ssz
    sseli
end
