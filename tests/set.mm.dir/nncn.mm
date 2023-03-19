include "cn.mm"
include "cc.mm"
include "nnsscn.mm"
include "sseli.mm"

theorem nncn
  let cA: class A


  assert |- ( A e. NN -> A e. CC )

  proof
    cn
    cc
    cA
    nnsscn
    sseli
end
