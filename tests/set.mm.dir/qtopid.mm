include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wfn.mm"
include "wa.mm"
include "cqtop.mm"
include "co.mm"
include "ccn.mm"
include "crn.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "wfo.mm"
include "simpr.mm"
include "dffn4.mm"
include "sylib.mm"
include "fof.mm"
include "syl.mm"
include "wss.mm"
include "wb.mm"
include "elqtop3.mm"
include "syldan.mm"
include "simplbda.mm"
include "ralrimiva.mm"
include "qtoptopon.mm"
include "iscn.mm"
include "mpbir2and.mm"

theorem qtopid
  let cF: class F
  let cJ: class J
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cY: class Y


  assert |- ( ( J e. ( TopOn ` X ) /\ F Fn X ) -> F e. ( J Cn ( J qTop F ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cF
    cX
    wfn
    #
    wa
    #
    cF
    cJ
    cJ
    cF
    cqtop
    co
    #
    ccn
    co
    wcel
    #
    cX
    cF
    crn
    #
    cF
    wf
    #
    cF
    ccnv
    vx
    cv
    #
    cima
    cJ
    wcel
    #
    vx
    @3
    wral
    #
    @2
    cX
    @5
    cF
    wfo
    #
    @6
    @2
    @1
    @10
    @0
    @1
    simpr
    cX
    cF
    dffn4
    sylib
    #
    cX
    @5
    cF
    fof
    syl
    @2
    @8
    vx
    @3
    @2
    @7
    @3
    wcel
    #
    @7
    @5
    wss
    #
    @8
    @0
    @1
    @10
    @12
    @13
    @8
    wa
    wb
    @11
    @7
    cF
    cJ
    cX
    @5
    elqtop3
    syldan
    simplbda
    ralrimiva
    @0
    @1
    @3
    @5
    ctopon
    cfv
    wcel
    #
    @4
    @6
    @9
    wa
    wb
    @0
    @1
    @10
    @14
    @11
    cF
    cJ
    cX
    @5
    qtoptopon
    syldan
    vx
    cF
    cJ
    @3
    cX
    @5
    iscn
    syldan
    mpbir2and
end
