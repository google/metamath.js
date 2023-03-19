include "cq.mm"
include "cc.mm"
include "qsscn.mm"
include "sseli.mm"

theorem qcn
  let cA: class A


  assert |- ( A e. QQ -> A e. CC )

  proof
    cq
    cc
    cA
    qsscn
    sseli
end
