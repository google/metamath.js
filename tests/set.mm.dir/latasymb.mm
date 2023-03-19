include "clat.mm"
include "wcel.mm"
include "cpo.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "wb.mm"
include "latpos.mm"
include "posasymb.mm"
include "syl3an1.mm"

theorem latasymb
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  assume latref.b: |- B = ( Base ` K )
  assume latref.l: |- .<_ = ( le ` K )


  assert |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> ( ( X .<_ Y /\ Y .<_ X ) <-> X = Y ) )

  proof
    cK
    clat
    wcel
    cK
    cpo
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
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
    wb
    cK
    latpos
    cB
    cK
    c.le
    cX
    cY
    latref.b
    latref.l
    posasymb
    syl3an1
end
