include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cuni.mm"
include "wceq.mm"
include "toponuni.mm"
include "ax-mp.mm"

theorem toponunii
  let cB: class B
  let cJ: class J
  assume topontopi.1: |- J e. ( TopOn ` B )


  assert |- B = U. J

  proof
    cJ
    cB
    ctopon
    cfv
    wcel
    cB
    cJ
    cuni
    wceq
    topontopi.1
    cB
    cJ
    toponuni
    ax-mp
end
