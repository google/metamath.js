include "crp.mm"
include "wcel.mm"
include "rpre.mm"
include "recnd.mm"

theorem rpcn
  let cA: class A


  assert |- ( A e. RR+ -> A e. CC )

  proof
    cA
    crp
    wcel
    cA
    cA
    rpre
    recnd
end
