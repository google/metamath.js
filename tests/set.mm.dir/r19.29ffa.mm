include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "ex.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "simpr.mm"
include "r19.29d2r.mm"
include "pm3.35.mm"
include "ancoms.mm"
include "rexlimivw.mm"
include "syl.mm"

theorem r19.29ffa
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume r19.29ffa.3: |- ( ( ( ( ph /\ x e. A ) /\ y e. B ) /\ ps ) -> ch )

  disjoint A y
  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint ch x
  disjoint ch y
  assert |- ( ( ph /\ E. x e. A E. y e. B ps ) -> ch )

  proof
    wph
    wps
    vy
    cB
    wrex
    vx
    cA
    wrex
    #
    wa
    #
    wps
    wch
    wi
    #
    wps
    wa
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    wch
    @1
    @2
    wps
    vx
    vy
    cA
    cB
    wph
    @2
    vy
    cB
    wral
    #
    vx
    cA
    wral
    @0
    wph
    @5
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    @2
    vy
    cB
    @6
    vy
    cv
    cB
    wcel
    wa
    wps
    wch
    r19.29ffa.3
    ex
    ralrimiva
    ralrimiva
    adantr
    wph
    @0
    simpr
    r19.29d2r
    @4
    wch
    vx
    cA
    @3
    wch
    vy
    cB
    wps
    @2
    wch
    wps
    wch
    pm3.35
    ancoms
    rexlimivw
    rexlimivw
    syl
end
