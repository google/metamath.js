include "wor.mm"
include "wpo.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "sopo.mm"
include "po2nr.mm"
include "sylan.mm"

theorem so2nr
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R


  assert |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) -> -. ( B R C /\ C R B ) )

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
    wa
    cB
    cC
    cR
    wbr
    cC
    cB
    cR
    wbr
    wa
    wn
    cA
    cR
    sopo
    cA
    cB
    cC
    cR
    po2nr
    sylan
end
