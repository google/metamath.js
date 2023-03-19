include "cop.mm"
include "cxp.mm"
include "wcel.mm"
include "opelxp.mm"
include "simprbi.mm"

theorem opelxp2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( <. A , B >. e. ( C X. D ) -> B e. D )

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
    cA
    cB
    cC
    cD
    opelxp
    simprbi
end
