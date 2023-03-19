include "ccom.mm"
include "coeq1i.mm"
include "coeq2i.mm"
include "eqtri.mm"

theorem coeq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume coeq12i.1: |- A = B
  assume coeq12i.2: |- C = D


  assert |- ( A o. C ) = ( B o. D )

  proof
    cA
    cC
    ccom
    cB
    cC
    ccom
    cB
    cD
    ccom
    cA
    cB
    cC
    coeq12i.1
    coeq1i
    cC
    cD
    cB
    coeq12i.2
    coeq2i
    eqtri
end
