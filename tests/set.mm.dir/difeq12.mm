include "wceq.mm"
include "cdif.mm"
include "difeq1.mm"
include "difeq2.mm"
include "sylan9eq.mm"

theorem difeq12
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A = B /\ C = D ) -> ( A \ C ) = ( B \ D ) )

  proof
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    cdif
    cB
    cC
    cdif
    cB
    cD
    cdif
    cA
    cB
    cC
    difeq1
    cC
    cD
    cB
    difeq2
    sylan9eq
end
