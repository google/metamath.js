include "wceq.mm"
include "wbr.mm"
include "breq1.mm"
include "breq2.mm"
include "sylan9bb.mm"

theorem breq12
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R


  assert |- ( ( A = B /\ C = D ) -> ( A R C <-> B R D ) )

  proof
    cA
    cB
    wceq
    cA
    cC
    cR
    wbr
    cB
    cC
    cR
    wbr
    cC
    cD
    wceq
    cB
    cD
    cR
    wbr
    cA
    cB
    cC
    cR
    breq1
    cC
    cD
    cB
    cR
    breq2
    sylan9bb
end
