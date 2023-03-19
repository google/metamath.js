include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ctop.mm"
include "cuni.mm"
include "topontop.mm"
include "toptopon2.mm"
include "sylib.mm"

theorem topontopon
  let cJ: class J
  let cX: class X


  assert |- ( J e. ( TopOn ` X ) -> J e. ( TopOn ` U. J ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    cJ
    ctop
    wcel
    cJ
    cJ
    cuni
    ctopon
    cfv
    wcel
    cX
    cJ
    topontop
    cJ
    toptopon2
    sylib
end
