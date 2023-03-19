include "wi.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "ex.mm"
include "ralrimiva.mm"
include "r19.29d2r.mm"
include "pm3.35.mm"
include "ancoms.mm"
include "rexlimivw.mm"
include "syl.mm"

theorem r19.29vva
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume r19.29vva.1: |- ( ( ( ( ph /\ x e. A ) /\ y e. B ) /\ ps ) -> ch )
  assume r19.29vva.2: |- ( ph -> E. x e. A E. y e. B ps )

  disjoint A y
  disjoint x y
  disjoint ch x
  disjoint ch y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ch )

  proof
    wph
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
    wph
    @0
    wps
    vx
    vy
    cA
    cB
    wph
    @0
    vy
    cB
    wral
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    @0
    vy
    cB
    @3
    vy
    cv
    cB
    wcel
    wa
    wps
    wch
    r19.29vva.1
    ex
    ralrimiva
    ralrimiva
    r19.29vva.2
    r19.29d2r
    @2
    wch
    vx
    cA
    @1
    wch
    vy
    cB
    wps
    @0
    wch
    wps
    wch
    pm3.35
    ancoms
    rexlimivw
    rexlimivw
    syl
end
