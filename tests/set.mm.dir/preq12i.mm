include "wceq.mm"
include "cpr.mm"
include "preq12.mm"
include "mp2an.mm"

theorem preq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume preq1i.1: |- A = B
  assume preq12i.2: |- C = D


  assert |- { A , C } = { B , D }

  proof
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    cpr
    cB
    cD
    cpr
    wceq
    preq1i.1
    preq12i.2
    cA
    cC
    cB
    cD
    preq12
    mp2an
end
