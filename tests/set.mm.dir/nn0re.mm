include "cn0.mm"
include "cr.mm"
include "nn0ssre.mm"
include "sseli.mm"

theorem nn0re
  let cA: class A


  assert |- ( A e. NN0 -> A e. RR )

  proof
    cn0
    cr
    cA
    nn0ssre
    sseli
end
