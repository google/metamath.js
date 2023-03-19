include "wor.mm"
include "wpo.mm"
include "wcel.mm"
include "cpred.mm"
include "wss.mm"
include "wi.mm"
include "sopo.mm"
include "predpo.mm"
include "sylan.mm"

theorem predso
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y


  assert |- ( ( R Or A /\ X e. A ) -> ( Y e. Pred ( R , A , X ) -> Pred ( R , A , Y ) C_ Pred ( R , A , X ) ) )

  proof
    cA
    cR
    wor
    cA
    cR
    wpo
    cX
    cA
    wcel
    cY
    cA
    cR
    cX
    cpred
    #
    wcel
    cA
    cR
    cY
    cpred
    @0
    wss
    wi
    cA
    cR
    sopo
    cA
    cR
    cX
    cY
    predpo
    sylan
end
