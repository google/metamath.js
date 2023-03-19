include "cpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "wa.mm"
include "pltval.mm"
include "wceq.mm"
include "posasymb.mm"
include "biimpd.mm"
include "expdimp.mm"
include "necon3ad.mm"
include "expimpd.mm"
include "sylbid.mm"
include "imp.mm"

theorem pltnle
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  assume pleval2.b: |- B = ( Base ` K )
  assume pleval2.l: |- .<_ = ( le ` K )
  assume pleval2.s: |- .< = ( lt ` K )


  assert |- ( ( ( K e. Poset /\ X e. B /\ Y e. B ) /\ X .< Y ) -> -. Y .<_ X )

  proof
    cK
    cpo
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    w3a
    #
    cX
    cY
    c.lt
    wbr
    #
    cY
    cX
    c.le
    wbr
    #
    wn
    #
    @0
    @1
    cX
    cY
    c.le
    wbr
    #
    cX
    cY
    wne
    #
    wa
    @3
    cpo
    cB
    cB
    c.lt
    cK
    c.le
    cX
    cY
    pleval2.l
    pleval2.s
    pltval
    @0
    @4
    @5
    @3
    @0
    @4
    wa
    @2
    cX
    cY
    @0
    @4
    @2
    cX
    cY
    wceq
    #
    @0
    @4
    @2
    wa
    @6
    cB
    cK
    c.le
    cX
    cY
    pleval2.b
    pleval2.l
    posasymb
    biimpd
    expdimp
    necon3ad
    expimpd
    sylbid
    imp
end
