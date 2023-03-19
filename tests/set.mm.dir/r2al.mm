include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "19.21v.mm"
include "r2allem.mm"

theorem r2al
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint A y
  assert |- ( A. x e. A A. y e. B ph <-> A. x A. y ( ( x e. A /\ y e. B ) -> ph ) )

  proof
    wph
    vx
    vy
    cA
    cB
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wcel
    wph
    wi
    vy
    19.21v
    r2allem
end
