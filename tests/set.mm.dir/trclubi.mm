include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cv.mm"
include "wss.mm"
include "ccom.mm"
include "wa.mm"
include "cab.mm"
include "wcel.mm"
include "cint.mm"
include "cun.mm"
include "wrel.mm"
include "wceq.mm"
include "relssdmrn.mm"
include "ssequn1.mm"
include "sylib.mm"
include "ax-mp.mm"
include "cvv.mm"
include "trclublem.mm"
include "eqeltrri.mm"
include "intss1.mm"

theorem trclubi
  let cR: class R
  let vs: setvar s
  assume trclubi.rel: |- Rel R
  assume trclubi.rex: |- R e. _V

  disjoint R s
  assert |- |^| { s | ( R C_ s /\ ( s o. s ) C_ s ) } C_ ( dom R X. ran R )

  proof
    cR
    cdm
    cR
    crn
    cxp
    #
    cR
    vs
    cv
    #
    wss
    @1
    @1
    ccom
    @1
    wss
    wa
    vs
    cab
    #
    wcel
    @2
    cint
    @0
    wss
    cR
    @0
    cun
    #
    @0
    @2
    cR
    wrel
    #
    @3
    @0
    wceq
    #
    trclubi.rel
    @4
    cR
    @0
    wss
    @5
    cR
    relssdmrn
    cR
    @0
    ssequn1
    sylib
    ax-mp
    cR
    cvv
    wcel
    @3
    @2
    wcel
    trclubi.rex
    vs
    cR
    cvv
    trclublem
    ax-mp
    eqeltrri
    @0
    @2
    intss1
    ax-mp
end
