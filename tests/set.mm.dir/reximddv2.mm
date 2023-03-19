include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "ex.mm"
include "reximdva.mm"
include "impr.mm"
include "reximddv.mm"

theorem reximddv2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume reximddv2.1: |- ( ( ( ( ph /\ x e. A ) /\ y e. B ) /\ ps ) -> ch )
  assume reximddv2.2: |- ( ph -> E. x e. A E. y e. B ps )

  disjoint A y
  disjoint ph x
  disjoint ph y
  disjoint x y
  assert |- ( ph -> E. x e. A E. y e. B ch )

  proof
    wph
    wps
    vy
    cB
    wrex
    #
    wch
    vy
    cB
    wrex
    #
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    #
    @0
    @1
    wph
    @2
    wa
    #
    wps
    wch
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
    reximddv2.1
    ex
    reximdva
    impr
    reximddv2.2
    reximddv
end
