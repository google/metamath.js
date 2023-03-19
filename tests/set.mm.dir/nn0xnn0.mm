include "cn0.mm"
include "cxnn0.mm"
include "nn0ssxnn0.mm"
include "sseli.mm"

theorem nn0xnn0
  let cA: class A


  assert |- ( A e. NN0 -> A e. NN0* )

  proof
    cn0
    cxnn0
    cA
    nn0ssxnn0
    sseli
end
