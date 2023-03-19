include "ctp.mm"
include "cpr.mm"
include "tprot.mm"
include "tpidm12.mm"
include "prcom.mm"
include "3eqtri.mm"

theorem tpidm23
  let cA: class A
  let cB: class B


  assert |- { A , B , B } = { A , B }

  proof
    cA
    cB
    cB
    ctp
    cB
    cB
    cA
    ctp
    cB
    cA
    cpr
    cA
    cB
    cpr
    cA
    cB
    cB
    tprot
    cB
    cA
    tpidm12
    cB
    cA
    prcom
    3eqtri
end
