include "ctop.mm"
include "wcel.mm"
include "c0.mm"
include "cnt.mm"
include "cfv.mm"
include "wceq.mm"
include "0opn.mm"
include "cuni.mm"
include "wss.mm"
include "wb.mm"
include "0ss.mm"
include "eqid.mm"
include "isopn3.mm"
include "mpan2.mm"
include "mpbid.mm"

theorem ntr0
  let cJ: class J


  assert |- ( J e. Top -> ( ( int ` J ) ` (/) ) = (/) )

  proof
    cJ
    ctop
    wcel
    #
    c0
    cJ
    wcel
    #
    c0
    cJ
    cnt
    cfv
    cfv
    c0
    wceq
    #
    cJ
    0opn
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
    isopn3
    mpan2
    mpbid
end
