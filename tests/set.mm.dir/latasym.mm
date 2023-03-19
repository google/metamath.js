include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "latasymb.mm"
include "biimpd.mm"

theorem latasym
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  assume latref.b: |- B = ( Base ` K )
  assume latref.l: |- .<_ = ( le ` K )


  assert |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> ( ( X .<_ Y /\ Y .<_ X ) -> X = Y ) )

  proof
    cK
    clat
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    w3a
    cX
    cY
    c.le
    wbr
    cY
    cX
    c.le
    wbr
    wa
    cX
    cY
    wceq
    cB
    cK
    c.le
    cX
    cY
    latref.b
    latref.l
    latasymb
    biimpd
end
