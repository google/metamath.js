include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "ccom.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "crn.mm"
include "cdm.mm"
include "cxp.mm"
include "cun.mm"
include "trclubg.mm"
include "rnss.mm"
include "syl.mm"
include "rnun.mm"
include "wceq.mm"
include "rnxpss.mm"
include "ssequn2.mm"
include "mpbi.mm"
include "eqtri.mm"
include "syl6sseq.mm"
include "ssmin.mm"
include "mp1i.mm"
include "eqssd.mm"

theorem rntrcl
  let vx: setvar x
  let cV: class V
  let cX: class X

  disjoint X x
  assert |- ( X e. V -> ran |^| { x | ( X C_ x /\ ( x o. x ) C_ x ) } = ran X )

  proof
    cX
    cV
    wcel
    #
    cX
    vx
    cv
    #
    wss
    @1
    @1
    ccom
    @1
    wss
    #
    wa
    vx
    cab
    cint
    #
    crn
    #
    cX
    crn
    #
    @0
    @4
    cX
    cX
    cdm
    #
    @5
    cxp
    #
    cun
    #
    crn
    #
    @5
    @0
    @3
    @8
    wss
    @4
    @9
    wss
    cX
    cV
    vx
    trclubg
    @3
    @8
    rnss
    syl
    @9
    @5
    @7
    crn
    #
    cun
    #
    @5
    cX
    @7
    rnun
    @10
    @5
    wss
    @11
    @5
    wceq
    @6
    @5
    rnxpss
    @10
    @5
    ssequn2
    mpbi
    eqtri
    syl6sseq
    cX
    @3
    wss
    @5
    @4
    wss
    @0
    @2
    vx
    cX
    ssmin
    cX
    @3
    rnss
    mp1i
    eqssd
end
