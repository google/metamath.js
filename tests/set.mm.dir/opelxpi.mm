include "cop.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "opelxp.mm"
include "biimpri.mm"

theorem opelxpi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A e. C /\ B e. D ) -> <. A , B >. e. ( C X. D ) )

  proof
    cA
    cB
    cop
    cC
    cD
    cxp
    wcel
    cA
    cC
    wcel
    cB
    cD
    wcel
    wa
    cA
    cB
    cC
    cD
    opelxp
    biimpri
end
