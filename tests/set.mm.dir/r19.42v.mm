include "wa.mm"
include "wrex.mm"
include "r19.41v.mm"
include "ancom.mm"
include "rexbii.mm"
include "3bitr4i.mm"

theorem r19.42v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A

  disjoint ph x
  assert |- ( E. x e. A ( ph /\ ps ) <-> ( ph /\ E. x e. A ps ) )

  proof
    wps
    wph
    wa
    #
    vx
    cA
    wrex
    wps
    vx
    cA
    wrex
    #
    wph
    wa
    wph
    wps
    wa
    #
    vx
    cA
    wrex
    wph
    @1
    wa
    wps
    wph
    vx
    cA
    r19.41v
    @2
    @0
    vx
    cA
    wph
    wps
    ancom
    rexbii
    wph
    @1
    ancom
    3bitr4i
end
