include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cdif.mm"
include "ccld.mm"
include "cfv.mm"
include "wb.mm"
include "difss.mm"
include "iscld2.mm"
include "mpan2.mm"
include "wceq.mm"
include "dfss4.mm"
include "biimpi.mm"
include "eleq1d.mm"
include "sylan9bb.mm"
include "bicomd.mm"

theorem isopn2
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume iscld.1: |- X = U. J


  assert |- ( ( J e. Top /\ S C_ X ) -> ( S e. J <-> ( X \ S ) e. ( Clsd ` J ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    wa
    cX
    cS
    cdif
    #
    cJ
    ccld
    cfv
    wcel
    #
    cS
    cJ
    wcel
    #
    @0
    @3
    cX
    @2
    cdif
    #
    cJ
    wcel
    #
    @1
    @4
    @0
    @2
    cX
    wss
    @3
    @6
    wb
    cX
    cS
    difss
    @2
    cJ
    cX
    iscld.1
    iscld2
    mpan2
    @1
    @5
    cS
    cJ
    @1
    @5
    cS
    wceq
    cS
    cX
    dfss4
    biimpi
    eleq1d
    sylan9bb
    bicomd
end
