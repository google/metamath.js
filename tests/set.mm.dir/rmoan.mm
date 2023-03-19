include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "wrmo.mm"
include "moan.mm"
include "an12.mm"
include "mobii.mm"
include "sylib.mm"
include "df-rmo.mm"
include "3imtr4i.mm"

theorem rmoan
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( E* x e. A ph -> E* x e. A ( ps /\ ph ) )

  proof
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    #
    vx
    wmo
    #
    @0
    wps
    wph
    wa
    #
    wa
    #
    vx
    wmo
    #
    wph
    vx
    cA
    wrmo
    @3
    vx
    cA
    wrmo
    @2
    wps
    @1
    wa
    #
    vx
    wmo
    @5
    @1
    wps
    vx
    moan
    @6
    @4
    vx
    wps
    @0
    wph
    an12
    mobii
    sylib
    wph
    vx
    cA
    df-rmo
    @3
    vx
    cA
    df-rmo
    3imtr4i
end
