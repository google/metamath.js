include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "clp.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "ccl.mm"
include "cab.mm"
include "lpval.mm"
include "difss.mm"
include "clsss.mm"
include "mp3an3.mm"
include "sseld.mm"
include "abssdv.mm"
include "eqsstrd.mm"

theorem lpsscls
  let cS: class S
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cT: class T
  assume lpfval.1: |- X = U. J


  assert |- ( ( J e. Top /\ S C_ X ) -> ( ( limPt ` J ) ` S ) C_ ( ( cls ` J ) ` S ) )

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
    #
    cS
    cJ
    clp
    cfv
    cfv
    vx
    cv
    #
    cS
    @3
    csn
    #
    cdif
    #
    cJ
    ccl
    cfv
    #
    cfv
    #
    wcel
    #
    vx
    cab
    cS
    @6
    cfv
    #
    vx
    cS
    cJ
    cX
    lpfval.1
    lpval
    @2
    @8
    vx
    @9
    @2
    @7
    @9
    @3
    @0
    @1
    @5
    cS
    wss
    @7
    @9
    wss
    cS
    @4
    difss
    cS
    @5
    cJ
    cX
    lpfval.1
    clsss
    mp3an3
    sseld
    abssdv
    eqsstrd
end
