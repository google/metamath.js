include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "anassrs.mm"
include "reximdva.mm"

theorem reximdvva
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume reximdvva.1: |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps -> ch ) )

  disjoint A y
  disjoint x y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( E. x e. A E. y e. B ps -> E. x e. A E. y e. B ch ) )

  proof
    wph
    wps
    vy
    cB
    wrex
    wch
    vy
    cB
    wrex
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    wps
    wch
    vy
    cB
    wph
    @0
    vy
    cv
    cB
    wcel
    wps
    wch
    wi
    reximdvva.1
    anassrs
    reximdva
    reximdva
end
