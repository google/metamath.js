include "wcel.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cun.mm"
include "cv.mm"
include "wss.mm"
include "ccom.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "trclublem.mm"
include "intss1.mm"
include "syl.mm"

theorem trclubg
  let cR: class R
  let cV: class V
  let vr: setvar r

  disjoint R r
  assert |- ( R e. V -> |^| { r | ( R C_ r /\ ( r o. r ) C_ r ) } C_ ( R u. ( dom R X. ran R ) ) )

  proof
    cR
    cV
    wcel
    cR
    cR
    cdm
    cR
    crn
    cxp
    cun
    #
    cR
    vr
    cv
    #
    wss
    @1
    @1
    ccom
    @1
    wss
    wa
    vr
    cab
    #
    wcel
    @2
    cint
    @0
    wss
    vr
    cR
    cV
    trclublem
    @0
    @2
    intss1
    syl
end
