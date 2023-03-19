include "wcel.mm"
include "wrel.mm"
include "wa.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cv.mm"
include "wss.mm"
include "ccom.mm"
include "cab.mm"
include "cint.mm"
include "cun.mm"
include "wceq.mm"
include "relssdmrn.mm"
include "ssequn1.mm"
include "sylib.mm"
include "trclublem.mm"
include "eleq1.mm"
include "biimpa.mm"
include "syl2anr.mm"
include "intss1.mm"
include "syl.mm"

theorem trclub
  let cR: class R
  let cV: class V
  let vr: setvar r

  disjoint R r
  assert |- ( ( R e. V /\ Rel R ) -> |^| { r | ( R C_ r /\ ( r o. r ) C_ r ) } C_ ( dom R X. ran R ) )

  proof
    cR
    cV
    wcel
    #
    cR
    wrel
    #
    wa
    cR
    cdm
    cR
    crn
    cxp
    #
    cR
    vr
    cv
    #
    wss
    @3
    @3
    ccom
    @3
    wss
    wa
    vr
    cab
    #
    wcel
    #
    @4
    cint
    @2
    wss
    @1
    cR
    @2
    cun
    #
    @2
    wceq
    #
    @6
    @4
    wcel
    #
    @5
    @0
    @1
    cR
    @2
    wss
    @7
    cR
    relssdmrn
    cR
    @2
    ssequn1
    sylib
    vr
    cR
    cV
    trclublem
    @7
    @8
    @5
    @6
    @2
    @4
    eleq1
    biimpa
    syl2anr
    @2
    @4
    intss1
    syl
end
