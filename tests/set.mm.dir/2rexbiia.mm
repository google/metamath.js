include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "rexbidva.mm"
include "rexbiia.mm"

theorem 2rexbiia
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume 2rexbiia.1: |- ( ( x e. A /\ y e. B ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint A y
  assert |- ( E. x e. A E. y e. B ph <-> E. x e. A E. y e. B ps )

  proof
    wph
    vy
    cB
    wrex
    wps
    vy
    cB
    wrex
    vx
    cA
    vx
    cv
    cA
    wcel
    wph
    wps
    vy
    cB
    2rexbiia.1
    rexbidva
    rexbiia
end
