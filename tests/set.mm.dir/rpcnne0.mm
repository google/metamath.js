include "crp.mm"
include "wcel.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "rpcn.mm"
include "rpne0.mm"
include "jca.mm"

theorem rpcnne0
  let cA: class A


  assert |- ( A e. RR+ -> ( A e. CC /\ A =/= 0 ) )

  proof
    cA
    crp
    wcel
    cA
    cc
    wcel
    cA
    cc0
    wne
    cA
    rpcn
    cA
    rpne0
    jca
end
