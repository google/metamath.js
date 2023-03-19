include "cv.mm"
include "ccnv.mm"
include "wceq.mm"
include "cmdv.mm"
include "cfv.mm"
include "cpw.mm"
include "crab.mm"
include "cmex.mm"
include "cfn.mm"
include "cin.mm"
include "cxp.mm"
include "cvv.mm"
include "eqid.mm"
include "mpstval.mm"
include "wss.mm"
include "xpss.mm"
include "ssv.mm"
include "xpss12.mm"
include "mp2an.mm"
include "eqsstri.mm"

theorem mpstssv
  let cP: class P
  let cT: class T
  let va: setvar a
  let vh: setvar h
  let vs: setvar s
  let vz: setvar z
  let cR: class R
  let vd: setvar d
  assume mpstssv.p: |- P = ( mPreSt ` T )


  assert |- P C_ ( ( _V X. _V ) X. _V )

  proof
    cP
    vd
    cv
    #
    ccnv
    @0
    wceq
    vd
    cT
    cmdv
    cfv
    #
    cpw
    crab
    #
    cT
    cmex
    cfv
    #
    cpw
    cfn
    cin
    #
    cxp
    #
    @3
    cxp
    #
    cvv
    cvv
    cxp
    #
    cvv
    cxp
    #
    cP
    cT
    @3
    @1
    vd
    @1
    eqid
    @3
    eqid
    mpstssv.p
    mpstval
    @5
    @7
    wss
    @3
    cvv
    wss
    @6
    @8
    wss
    @2
    @4
    xpss
    @3
    ssv
    @5
    @7
    @3
    cvv
    xpss12
    mp2an
    eqsstri
end
