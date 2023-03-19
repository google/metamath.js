include "cv.mm"
include "ccom.mm"
include "wss.mm"
include "clsslem.mm"

theorem trclsslem
  let cR: class R
  let cS: class S
  let vr: setvar r

  disjoint R r
  disjoint S r
  assert |- ( R C_ S -> |^| { r | ( R C_ r /\ ( r o. r ) C_ r ) } C_ |^| { r | ( S C_ r /\ ( r o. r ) C_ r ) } )

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
    clsslem
end
