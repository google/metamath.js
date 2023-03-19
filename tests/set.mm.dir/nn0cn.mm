include "cn0.mm"
include "cc.mm"
include "nn0sscn.mm"
include "sseli.mm"

theorem nn0cn
  let cA: class A


  assert |- ( A e. NN0 -> A e. CC )

  proof
    cn0
    cc
    cA
    nn0sscn
    sseli
end
