include "wceq.mm"
include "cxrn.mm"
include "xrneq12.mm"
include "mp2an.mm"

theorem xrneq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume xrneq12i.1: |- A = B
  assume xrneq12i.2: |- C = D


  assert |- ( A |X. C ) = ( B |X. D )

  proof
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    cxrn
    cB
    cD
    cxrn
    wceq
    xrneq12i.1
    xrneq12i.2
    cA
    cB
    cC
    cD
    xrneq12
    mp2an
end
