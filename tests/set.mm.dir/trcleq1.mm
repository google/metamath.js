include "cv.mm"
include "ccom.mm"
include "wss.mm"
include "cleq1.mm"

theorem trcleq1
  let cR: class R
  let cS: class S
  let vr: setvar r

  disjoint R r
  disjoint S r
  assert |- ( R = S -> |^| { r | ( R C_ r /\ ( r o. r ) C_ r ) } = |^| { r | ( S C_ r /\ ( r o. r ) C_ r ) } )

  proof
    vr
    cv
    #
    @0
    ccom
    @0
    wss
    cR
    cS
    vr
    cleq1
end
