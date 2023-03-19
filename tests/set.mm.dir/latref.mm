include "clat.mm"
include "wcel.mm"
include "cpo.mm"
include "wbr.mm"
include "latpos.mm"
include "posref.mm"
include "sylan.mm"

theorem latref
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  assume latref.b: |- B = ( Base ` K )
  assume latref.l: |- .<_ = ( le ` K )


  assert |- ( ( K e. Lat /\ X e. B ) -> X .<_ X )

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
    cX
    cX
    c.le
    wbr
    cK
    latpos
    cB
    cK
    c.le
    cX
    latref.b
    latref.l
    posref
    sylan
end
