include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wss.mm"
include "ccom.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "ctcl.mm"
include "cfv.mm"
include "wceq.mm"
include "elex.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cun.mm"
include "trclexlem.mm"
include "trclubg.mm"
include "ssexd.mm"
include "jccir.mm"
include "trcleq1.mm"
include "df-trcl.mm"
include "fvmptg.mm"
include "syl.mm"

theorem trclfv
  let vx: setvar x
  let cR: class R
  let cV: class V
  let vr: setvar r

  disjoint R x
  disjoint r x
  disjoint R r
  assert |- ( R e. V -> ( t+ ` R ) = |^| { x | ( R C_ x /\ ( x o. x ) C_ x ) } )

  proof
    cR
    cV
    wcel
    #
    cR
    cvv
    wcel
    #
    cR
    vx
    cv
    #
    wss
    @2
    @2
    ccom
    @2
    wss
    #
    wa
    vx
    cab
    cint
    #
    cvv
    wcel
    #
    wa
    cR
    ctcl
    cfv
    @4
    wceq
    @0
    @1
    @5
    cR
    cV
    elex
    @1
    @4
    cR
    cR
    cdm
    cR
    crn
    cxp
    cun
    cvv
    cR
    cvv
    trclexlem
    cR
    cvv
    vx
    trclubg
    ssexd
    jccir
    vr
    cR
    vr
    cv
    #
    @2
    wss
    @3
    wa
    vx
    cab
    cint
    @4
    cvv
    cvv
    ctcl
    @6
    cR
    vx
    trcleq1
    vr
    vx
    df-trcl
    fvmptg
    syl
end
