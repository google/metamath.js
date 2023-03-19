include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "anassrs.mm"
include "ralimdva.mm"

theorem ralimdvva
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume ralimdvva.1: |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps -> ch ) )

  disjoint A y
  disjoint x y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( A. x e. A A. y e. B ps -> A. x e. A A. y e. B ch ) )

  proof
    wph
    wps
    vy
    cB
    wral
    wch
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
    ralimdvva.1
    anassrs
    ralimdva
    ralimdva
end
