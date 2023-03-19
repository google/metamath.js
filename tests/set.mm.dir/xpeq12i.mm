include "wceq.mm"
include "cxp.mm"
include "xpeq12.mm"
include "mp2an.mm"

theorem xpeq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume xpeq12i.1: |- A = B
  assume xpeq12i.2: |- C = D


  assert |- ( A X. C ) = ( B X. D )

  proof
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    cxp
    cB
    cD
    cxp
    wceq
    xpeq12i.1
    xpeq12i.2
    cA
    cB
    cC
    cD
    xpeq12
    mp2an
end
