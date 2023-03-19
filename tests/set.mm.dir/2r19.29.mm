include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "r19.29.mm"
include "reximi.mm"
include "syl.mm"

theorem 2r19.29
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B


  assert |- ( ( A. x e. A A. y e. B ph /\ E. x e. A E. y e. B ps ) -> E. x e. A E. y e. B ( ph /\ ps ) )

  proof
    wph
    vy
    cB
    wral
    #
    vx
    cA
    wral
    wps
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    wa
    @0
    @1
    wa
    #
    vx
    cA
    wrex
    wph
    wps
    wa
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    @0
    @1
    vx
    cA
    r19.29
    @2
    @3
    vx
    cA
    wph
    wps
    vy
    cB
    r19.29
    reximi
    syl
end
