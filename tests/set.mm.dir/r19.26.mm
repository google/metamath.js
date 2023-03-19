include "wa.mm"
include "wral.mm"
include "simpl.mm"
include "ralimi.mm"
include "simpr.mm"
include "jca.mm"
include "pm3.2.mm"
include "ral2imi.mm"
include "imp.mm"
include "impbii.mm"

theorem r19.26
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( A. x e. A ( ph /\ ps ) <-> ( A. x e. A ph /\ A. x e. A ps ) )

  proof
    wph
    wps
    wa
    #
    vx
    cA
    wral
    #
    wph
    vx
    cA
    wral
    #
    wps
    vx
    cA
    wral
    #
    wa
    @1
    @2
    @3
    @0
    wph
    vx
    cA
    wph
    wps
    simpl
    ralimi
    @0
    wps
    vx
    cA
    wph
    wps
    simpr
    ralimi
    jca
    @2
    @3
    @1
    wph
    wps
    @0
    vx
    cA
    wph
    wps
    pm3.2
    ral2imi
    imp
    impbii
end
