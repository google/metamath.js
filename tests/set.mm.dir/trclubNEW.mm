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
include "trclubgNEW.mm"
include "wceq.mm"
include "wrel.mm"
include "relssdmrn.mm"
include "syl.mm"
include "ssequn1.mm"
include "sylib.mm"
include "sseqtrd.mm"

theorem trclubNEW
  let wph: wff ph
  let vx: setvar x
  let cR: class R
  assume trclubNEW.rex: |- ( ph -> R e. _V )
  assume trclubNEW.rel: |- ( ph -> Rel R )

  disjoint R x
  assert |- ( ph -> |^| { x | ( R C_ x /\ ( x o. x ) C_ x ) } C_ ( dom R X. ran R ) )

  proof
    wph
    cR
    vx
    cv
    #
    wss
    @0
    @0
    ccom
    @0
    wss
    wa
    vx
    cab
    cint
    cR
    cR
    cdm
    cR
    crn
    cxp
    #
    cun
    #
    @1
    wph
    vx
    cR
    trclubNEW.rex
    trclubgNEW
    wph
    cR
    @1
    wss
    #
    @2
    @1
    wceq
    wph
    cR
    wrel
    @3
    trclubNEW.rel
    cR
    relssdmrn
    syl
    cR
    @1
    ssequn1
    sylib
    sseqtrd
end
