include "cn.mm"
include "cr.mm"
include "nnssre.mm"
include "sseli.mm"

theorem nnre
  let cA: class A


  assert |- ( A e. NN -> A e. RR )

  proof
    cn
    cr
    cA
    nnssre
    sseli
end
