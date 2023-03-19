include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "r19.29.mm"
include "ancom.mm"
include "rexbii.mm"
include "3imtr4i.mm"

theorem r19.29r
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( ( E. x e. A ph /\ A. x e. A ps ) -> E. x e. A ( ph /\ ps ) )

  proof
    wps
    vx
    cA
    wral
    #
    wph
    vx
    cA
    wrex
    #
    wa
    wps
    wph
    wa
    #
    vx
    cA
    wrex
    @1
    @0
    wa
    wph
    wps
    wa
    #
    vx
    cA
    wrex
    wps
    wph
    vx
    cA
    r19.29
    @1
    @0
    ancom
    @3
    @2
    vx
    cA
    wph
    wps
    ancom
    rexbii
    3imtr4i
end
