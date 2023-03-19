include "wceq.mm"
include "cin.mm"
include "ineq12.mm"
include "mp2an.mm"

theorem ineq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ineq1i.1: |- A = B
  assume ineq12i.2: |- C = D


  assert |- ( A i^i C ) = ( B i^i D )

  proof
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    cin
    cB
    cD
    cin
    wceq
    ineq1i.1
    ineq12i.2
    cA
    cB
    cC
    cD
    ineq12
    mp2an
end
