include "wceq.mm"
include "eqeq1i.mm"
include "eqeq2i.mm"
include "bitri.mm"

theorem eqeq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume eqeq12i.1: |- A = B
  assume eqeq12i.2: |- C = D


  assert |- ( A = C <-> B = D )

  proof
    cA
    cC
    wceq
    cB
    cC
    wceq
    cB
    cD
    wceq
    cA
    cB
    cC
    eqeq12i.1
    eqeq1i
    cC
    cD
    cB
    eqeq12i.2
    eqeq2i
    bitri
end
