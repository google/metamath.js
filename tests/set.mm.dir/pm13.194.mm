include "weq.mm"
include "wa.mm"
include "wsb.mm"
include "w3a.mm"
include "cv.mm"
include "wsbc.mm"
include "pm13.13a.mm"
include "sbsbc.mm"
include "sylibr.mm"
include "simpl.mm"
include "simpr.mm"
include "3jca.mm"
include "3simpc.mm"
include "impbii.mm"

theorem pm13.194
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ph /\ x = y ) <-> ( [ y / x ] ph /\ ph /\ x = y ) )

  proof
    wph
    vx
    vy
    weq
    #
    wa
    #
    wph
    vx
    vy
    wsb
    #
    wph
    @0
    w3a
    @1
    @2
    wph
    @0
    @1
    wph
    vx
    vy
    cv
    #
    wsbc
    @2
    wph
    vx
    @3
    pm13.13a
    wph
    vx
    vy
    sbsbc
    sylibr
    wph
    @0
    simpl
    wph
    @0
    simpr
    3jca
    @2
    wph
    @0
    3simpc
    impbii
end
