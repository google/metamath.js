include "wor.mm"
include "wpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "sopo.mm"
include "potr.mm"
include "sylan.mm"

theorem sotr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R


  assert |- ( ( R Or A /\ ( B e. A /\ C e. A /\ D e. A ) ) -> ( ( B R C /\ C R D ) -> B R D ) )

  proof
    cA
    cR
    wor
    cA
    cR
    wpo
    cB
    cA
    wcel
    cC
    cA
    wcel
    cD
    cA
    wcel
    w3a
    cB
    cC
    cR
    wbr
    cC
    cD
    cR
    wbr
    wa
    cB
    cD
    cR
    wbr
    wi
    cA
    cR
    sopo
    cA
    cB
    cC
    cD
    cR
    potr
    sylan
end
