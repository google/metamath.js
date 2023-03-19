include "wss.mm"
include "cv.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "sstr2.mm"
include "anim1d.mm"
include "ss2abdv.mm"
include "intss.mm"
include "syl.mm"

theorem clsslem
  let wph: wff ph
  let cR: class R
  let cS: class S
  let vr: setvar r

  disjoint R r
  disjoint S r
  assert |- ( R C_ S -> |^| { r | ( R C_ r /\ ph ) } C_ |^| { r | ( S C_ r /\ ph ) } )

  proof
    cR
    cS
    wss
    #
    cS
    vr
    cv
    #
    wss
    #
    wph
    wa
    #
    vr
    cab
    #
    cR
    @1
    wss
    #
    wph
    wa
    #
    vr
    cab
    #
    wss
    @7
    cint
    @4
    cint
    wss
    @0
    @3
    @6
    vr
    @0
    @2
    @5
    wph
    cR
    cS
    @1
    sstr2
    anim1d
    ss2abdv
    @4
    @7
    intss
    syl
end
