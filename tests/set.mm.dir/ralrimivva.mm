include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "ex.mm"
include "ralrimivv.mm"

theorem ralrimivva
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume ralrimivva.1: |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ps )

  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint A y
  assert |- ( ph -> A. x e. A A. y e. B ps )

  proof
    wph
    wps
    vx
    vy
    cA
    cB
    wph
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wcel
    wa
    wps
    ralrimivva.1
    ex
    ralrimivv
end
