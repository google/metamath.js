include "cvv.mm"
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
include "mp2b.mm"

theorem trclubgi
  let cR: class R
  let vs: setvar s
  assume trclubgi.rex: |- R e. _V

  disjoint R s
  assert |- |^| { s | ( R C_ s /\ ( s o. s ) C_ s ) } C_ ( R u. ( dom R X. ran R ) )

  proof
    cR
    cvv
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
    trclubgi.rex
    vs
    cR
    cvv
    trclublem
    @0
    @2
    intss1
    mp2b
end
