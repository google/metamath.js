include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "ralrimiva.mm"
include "rgen.mm"

theorem rgen2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume rgen2.1: |- ( ( x e. A /\ y e. B ) -> ph )

  disjoint x y
  disjoint A y
  assert |- A. x e. A A. y e. B ph

  proof
    wph
    vy
    cB
    wral
    vx
    cA
    vx
    cv
    cA
    wcel
    wph
    vy
    cB
    rgen2.1
    ralrimiva
    rgen
end
