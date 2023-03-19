include "cn.mm"
include "cq.mm"
include "nnssq.mm"
include "sseli.mm"

theorem nnq
  let cA: class A


  assert |- ( A e. NN -> A e. QQ )

  proof
    cn
    cq
    cA
    nnssq
    sseli
end
