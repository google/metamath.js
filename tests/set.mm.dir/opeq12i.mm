include "wceq.mm"
include "cop.mm"
include "opeq12.mm"
include "mp2an.mm"

theorem opeq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume opeq1i.1: |- A = B
  assume opeq12i.2: |- C = D


  assert |- <. A , C >. = <. B , D >.

  proof
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    cop
    cB
    cD
    cop
    wceq
    opeq1i.1
    opeq12i.2
    cA
    cC
    cB
    cD
    opeq12
    mp2an
end
