include "wor.mm"
include "wpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "sopo.mm"
include "po3nr.mm"
include "sylan.mm"

theorem so3nr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R


  assert |- ( ( R Or A /\ ( B e. A /\ C e. A /\ D e. A ) ) -> -. ( B R C /\ C R D /\ D R B ) )

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
    cD
    cB
    cR
    wbr
    w3a
    wn
    cA
    cR
    sopo
    cA
    cB
    cC
    cD
    cR
    po3nr
    sylan
end
