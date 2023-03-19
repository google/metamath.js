include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ctop.mm"
include "cuni.mm"
include "wceq.mm"
include "istopon.mm"
include "simplbi.mm"

theorem topontop
  let cB: class B
  let cJ: class J


  assert |- ( J e. ( TopOn ` B ) -> J e. Top )

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
    simplbi
end
