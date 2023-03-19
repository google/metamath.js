include "ctmd.mm"
include "wcel.mm"
include "ctps.mm"
include "ctopon.mm"
include "cfv.mm"
include "tmdtps.mm"
include "istps.mm"
include "sylib.mm"

theorem tmdtopon
  let cG: class G
  let cJ: class J
  let cX: class X
  assume tgpcn.j: |- J = ( TopOpen ` G )
  assume tgptopon.x: |- X = ( Base ` G )


  assert |- ( G e. TopMnd -> J e. ( TopOn ` X ) )

  proof
    cG
    ctmd
    wcel
    cG
    ctps
    wcel
    cJ
    cX
    ctopon
    cfv
    wcel
    cG
    tmdtps
    cX
    cJ
    cG
    tgptopon.x
    tgpcn.j
    istps
    sylib
end
