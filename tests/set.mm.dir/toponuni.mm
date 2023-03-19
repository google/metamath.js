include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ctop.mm"
include "cuni.mm"
include "wceq.mm"
include "istopon.mm"
include "simprbi.mm"

theorem toponuni
  let cB: class B
  let cJ: class J


  assert |- ( J e. ( TopOn ` B ) -> B = U. J )

  proof
    cJ
    cB
    ctopon
    cfv
    wcel
    cJ
    ctop
    wcel
    cB
    cJ
    cuni
    wceq
    cB
    cJ
    istopon
    simprbi
end
