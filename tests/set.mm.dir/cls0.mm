include "ctop.mm"
include "wcel.mm"
include "c0.mm"
include "ccld.mm"
include "cfv.mm"
include "ccl.mm"
include "wceq.mm"
include "0cld.mm"
include "cuni.mm"
include "wss.mm"
include "wb.mm"
include "0ss.mm"
include "eqid.mm"
include "iscld3.mm"
include "mpan2.mm"
include "mpbid.mm"

theorem cls0
  let cJ: class J


  assert |- ( J e. Top -> ( ( cls ` J ) ` (/) ) = (/) )

  proof
    cJ
    ctop
    wcel
    #
    c0
    cJ
    ccld
    cfv
    wcel
    #
    c0
    cJ
    ccl
    cfv
    cfv
    c0
    wceq
    #
    cJ
    0cld
    @0
    c0
    cJ
    cuni
    #
    wss
    @1
    @2
    wb
    @3
    0ss
    c0
    cJ
    @3
    @3
    eqid
    iscld3
    mpan2
    mpbid
end
