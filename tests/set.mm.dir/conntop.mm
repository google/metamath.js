include "cconn.mm"
include "wcel.mm"
include "ctop.mm"
include "ccld.mm"
include "cfv.mm"
include "cin.mm"
include "c0.mm"
include "cuni.mm"
include "cpr.mm"
include "wceq.mm"
include "eqid.mm"
include "isconn.mm"
include "simplbi.mm"

theorem conntop
  let cJ: class J


  assert |- ( J e. Conn -> J e. Top )

  proof
    cJ
    cconn
    wcel
    cJ
    ctop
    wcel
    cJ
    cJ
    ccld
    cfv
    cin
    c0
    cJ
    cuni
    #
    cpr
    wceq
    cJ
    @0
    @0
    eqid
    isconn
    simplbi
end
