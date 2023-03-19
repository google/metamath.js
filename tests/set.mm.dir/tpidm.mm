include "ctp.mm"
include "cpr.mm"
include "csn.mm"
include "tpidm12.mm"
include "dfsn2.mm"
include "eqtr4i.mm"

theorem tpidm
  let cA: class A


  assert |- { A , A , A } = { A }

  proof
    cA
    cA
    cA
    ctp
    cA
    cA
    cpr
    cA
    csn
    cA
    cA
    tpidm12
    cA
    dfsn2
    eqtr4i
end
