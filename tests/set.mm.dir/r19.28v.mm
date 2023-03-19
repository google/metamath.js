include "wral.mm"
include "wa.mm"
include "r19.27v.mm"
include "ancom.mm"
include "ralbii.mm"
include "3imtr4i.mm"

theorem r19.28v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A

  disjoint ph x
  assert |- ( ( ph /\ A. x e. A ps ) -> A. x e. A ( ph /\ ps ) )

  proof
    wps
    vx
    cA
    wral
    #
    wph
    wa
    wps
    wph
    wa
    #
    vx
    cA
    wral
    wph
    @0
    wa
    wph
    wps
    wa
    #
    vx
    cA
    wral
    wps
    wph
    vx
    cA
    r19.27v
    wph
    @0
    ancom
    @2
    @1
    vx
    cA
    wph
    wps
    ancom
    ralbii
    3imtr4i
end
