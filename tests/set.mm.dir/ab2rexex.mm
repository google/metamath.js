include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "abrexex.mm"
include "abrexex2.mm"

theorem ab2rexex
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  assume ab2rexex.1: |- A e. _V
  assume ab2rexex.2: |- B e. _V

  disjoint x z
  disjoint A x
  disjoint A z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C z
  assert |- { z | E. x e. A E. y e. B z = C } e. _V

  proof
    vz
    cv
    cC
    wceq
    vy
    cB
    wrex
    vx
    vz
    cA
    ab2rexex.1
    vy
    vz
    cB
    cC
    ab2rexex.2
    abrexex
    abrexex2
end
