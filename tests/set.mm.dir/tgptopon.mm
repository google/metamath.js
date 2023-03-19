include "ctgp.mm"
include "wcel.mm"
include "ctps.mm"
include "ctopon.mm"
include "cfv.mm"
include "tgptps.mm"
include "istps.mm"
include "sylib.mm"

theorem tgptopon
  let cG: class G
  let cJ: class J
  let cX: class X
  assume tgpcn.j: |- J = ( TopOpen ` G )
  assume tgptopon.x: |- X = ( Base ` G )


  assert |- ( G e. TopGrp -> J e. ( TopOn ` X ) )

  proof
    cG
    ctgp
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
    tgptps
    cX
    cJ
    cG
    tgptopon.x
    tgpcn.j
    istps
    sylib
end
