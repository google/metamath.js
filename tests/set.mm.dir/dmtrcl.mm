include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "ccom.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cun.mm"
include "trclubg.mm"
include "dmss.mm"
include "syl.mm"
include "dmun.mm"
include "wceq.mm"
include "dmxpss.mm"
include "ssequn2.mm"
include "mpbi.mm"
include "eqtri.mm"
include "syl6sseq.mm"
include "ssmin.mm"
include "mp1i.mm"
include "eqssd.mm"

theorem dmtrcl
  let vx: setvar x
  let cV: class V
  let cX: class X

  disjoint X x
  assert |- ( X e. V -> dom |^| { x | ( X C_ x /\ ( x o. x ) C_ x ) } = dom X )

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
    cdm
    #
    cX
    cdm
    #
    @0
    @4
    cX
    @5
    cX
    crn
    #
    cxp
    #
    cun
    #
    cdm
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
    dmss
    syl
    @9
    @5
    @7
    cdm
    #
    cun
    #
    @5
    cX
    @7
    dmun
    @10
    @5
    wss
    @11
    @5
    wceq
    @5
    @6
    dmxpss
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
    dmss
    mp1i
    eqssd
end
