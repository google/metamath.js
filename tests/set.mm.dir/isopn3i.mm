include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "cnt.mm"
include "cfv.mm"
include "wceq.mm"
include "simpr.mm"
include "cuni.mm"
include "wss.mm"
include "wb.mm"
include "elssuni.mm"
include "eqid.mm"
include "isopn3.mm"
include "sylan2.mm"
include "mpbid.mm"

theorem isopn3i
  let cS: class S
  let cJ: class J


  assert |- ( ( J e. Top /\ S e. J ) -> ( ( int ` J ) ` S ) = S )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cJ
    wcel
    #
    wa
    @1
    cS
    cJ
    cnt
    cfv
    cfv
    cS
    wceq
    #
    @0
    @1
    simpr
    @1
    @0
    cS
    cJ
    cuni
    #
    wss
    @1
    @2
    wb
    cS
    cJ
    elssuni
    cS
    cJ
    @3
    @3
    eqid
    isopn3
    sylan2
    mpbid
end
