include "wrex.mm"
include "abrexex2.mm"

theorem ab2rexex2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume ab2rexex2.1: |- A e. _V
  assume ab2rexex2.2: |- B e. _V
  assume ab2rexex2.3: |- { z | ph } e. _V

  disjoint x z
  disjoint A x
  disjoint A z
  disjoint y z
  disjoint B y
  disjoint B z
  assert |- { z | E. x e. A E. y e. B ph } e. _V

  proof
    wph
    vy
    cB
    wrex
    vx
    vz
    cA
    ab2rexex2.1
    wph
    vy
    vz
    cB
    ab2rexex2.2
    ab2rexex2.3
    abrexex2
    abrexex2
end
