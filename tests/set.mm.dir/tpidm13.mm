include "ctp.mm"
include "cpr.mm"
include "tprot.mm"
include "tpidm12.mm"
include "eqtr3i.mm"

theorem tpidm13
  let cA: class A
  let cB: class B


  assert |- { A , B , A } = { A , B }

  proof
    cA
    cA
    cB
    ctp
    cA
    cB
    cA
    ctp
    cA
    cB
    cpr
    cA
    cA
    cB
    tprot
    cA
    cB
    tpidm12
    eqtr3i
end
