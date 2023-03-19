include "clat.mm"
include "wcel.mm"
include "cpo.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "latpos.mm"
include "postr.mm"
include "sylan.mm"

theorem lattr
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume latref.b: |- B = ( Base ` K )
  assume latref.l: |- .<_ = ( le ` K )


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .<_ Y /\ Y .<_ Z ) -> X .<_ Z ) )

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
    cZ
    cB
    wcel
    w3a
    cX
    cY
    c.le
    wbr
    cY
    cZ
    c.le
    wbr
    wa
    cX
    cZ
    c.le
    wbr
    wi
    cK
    latpos
    cB
    cK
    c.le
    cX
    cY
    cZ
    latref.b
    latref.l
    postr
    sylan
end
