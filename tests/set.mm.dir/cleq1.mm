include "wceq.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "cab.mm"
include "cleq1lem.mm"
include "abbidv.mm"
include "inteqd.mm"

theorem cleq1
  let wph: wff ph
  let cR: class R
  let cS: class S
  let vr: setvar r

  disjoint R r
  disjoint S r
  assert |- ( R = S -> |^| { r | ( R C_ r /\ ph ) } = |^| { r | ( S C_ r /\ ph ) } )

  proof
    cR
    cS
    wceq
    #
    cR
    vr
    cv
    #
    wss
    wph
    wa
    #
    vr
    cab
    cS
    @1
    wss
    wph
    wa
    #
    vr
    cab
    @0
    @2
    @3
    vr
    wph
    cR
    cS
    @1
    cleq1lem
    abbidv
    inteqd
end
