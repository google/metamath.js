include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "cdif.mm"
include "ccld.mm"
include "cfv.mm"
include "simpr.mm"
include "wss.mm"
include "wb.mm"
include "eltopss.mm"
include "isopn2.mm"
include "syldan.mm"
include "mpbid.mm"

theorem opncld
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume iscld.1: |- X = U. J


  assert |- ( ( J e. Top /\ S e. J ) -> ( X \ S ) e. ( Clsd ` J ) )

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
    cX
    cS
    cdif
    cJ
    ccld
    cfv
    wcel
    #
    @0
    @1
    simpr
    @0
    @1
    cS
    cX
    wss
    @1
    @2
    wb
    cS
    cJ
    cX
    iscld.1
    eltopss
    cS
    cJ
    cX
    iscld.1
    isopn2
    syldan
    mpbid
end
