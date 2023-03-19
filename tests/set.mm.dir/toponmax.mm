include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cuni.mm"
include "toponuni.mm"
include "ctop.mm"
include "topontop.mm"
include "eqid.mm"
include "topopn.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem toponmax
  let cB: class B
  let cJ: class J


  assert |- ( J e. ( TopOn ` B ) -> B e. J )

  proof
    cJ
    cB
    ctopon
    cfv
    wcel
    #
    cB
    cJ
    cuni
    #
    cJ
    cB
    cJ
    toponuni
    @0
    cJ
    ctop
    wcel
    @1
    cJ
    wcel
    cB
    cJ
    topontop
    cJ
    @1
    @1
    eqid
    topopn
    syl
    eqeltrd
end
