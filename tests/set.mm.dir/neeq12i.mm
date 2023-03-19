include "eqeq12i.mm"
include "necon3bii.mm"

theorem neeq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume neeq1i.1: |- A = B
  assume neeq12i.2: |- C = D


  assert |- ( A =/= C <-> B =/= D )

  proof
    cA
    cC
    cB
    cD
    cA
    cB
    cC
    cD
    neeq1i.1
    neeq12i.2
    eqeq12i
    necon3bii
end
