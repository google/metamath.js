include "wa.mm"
include "wrex.mm"
include "simpl.mm"
include "reximi.mm"
include "simpr.mm"
include "jca.mm"

theorem r19.40
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( E. x e. A ( ph /\ ps ) -> ( E. x e. A ph /\ E. x e. A ps ) )

  proof
    wph
    wps
    wa
    #
    vx
    cA
    wrex
    wph
    vx
    cA
    wrex
    wps
    vx
    cA
    wrex
    @0
    wph
    vx
    cA
    wph
    wps
    simpl
    reximi
    @0
    wps
    vx
    cA
    wph
    wps
    simpr
    reximi
    jca
end
