include "wor.mm"
include "wpo.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "sopo.mm"
include "poirr.mm"
include "sylan.mm"

theorem sonr
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( ( R Or A /\ B e. A ) -> -. B R B )

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
    cB
    cB
    cR
    wbr
    wn
    cA
    cR
    sopo
    cA
    cB
    cR
    poirr
    sylan
end
