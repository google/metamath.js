include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "sotric.mm"
include "pm2.46.mm"
include "syl6bi.mm"

theorem soasym
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y


  assert |- ( ( R Or A /\ ( X e. A /\ Y e. A ) ) -> ( X R Y -> -. Y R X ) )

  proof
    cA
    cR
    wor
    cX
    cA
    wcel
    cY
    cA
    wcel
    wa
    wa
    cX
    cY
    cR
    wbr
    cX
    cY
    wceq
    #
    cY
    cX
    cR
    wbr
    #
    wo
    wn
    @1
    wn
    cA
    cX
    cY
    cR
    sotric
    @0
    @1
    pm2.46
    syl6bi
end
