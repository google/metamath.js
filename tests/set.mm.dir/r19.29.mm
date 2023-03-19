include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "pm3.2.mm"
include "ralimi.mm"
include "rexim.mm"
include "syl.mm"
include "imp.mm"

theorem r19.29
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( ( A. x e. A ph /\ E. x e. A ps ) -> E. x e. A ( ph /\ ps ) )

  proof
    wph
    vx
    cA
    wral
    #
    wps
    vx
    cA
    wrex
    #
    wph
    wps
    wa
    #
    vx
    cA
    wrex
    #
    @0
    wps
    @2
    wi
    #
    vx
    cA
    wral
    @1
    @3
    wi
    wph
    @4
    vx
    cA
    wph
    wps
    pm3.2
    ralimi
    wps
    @2
    vx
    cA
    rexim
    syl
    imp
end
