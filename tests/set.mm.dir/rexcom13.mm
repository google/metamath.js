include "wrex.mm"
include "rexcom.mm"
include "rexbii.mm"
include "3bitri.mm"

theorem rexcom13
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint x z
  disjoint B x
  disjoint B z
  disjoint x y
  disjoint C x
  disjoint C y
  assert |- ( E. x e. A E. y e. B E. z e. C ph <-> E. z e. C E. y e. B E. x e. A ph )

  proof
    wph
    vz
    cC
    wrex
    #
    vy
    cB
    wrex
    vx
    cA
    wrex
    @0
    vx
    cA
    wrex
    #
    vy
    cB
    wrex
    wph
    vx
    cA
    wrex
    #
    vz
    cC
    wrex
    #
    vy
    cB
    wrex
    @2
    vy
    cB
    wrex
    vz
    cC
    wrex
    @0
    vx
    vy
    cA
    cB
    rexcom
    @1
    @3
    vy
    cB
    wph
    vx
    vz
    cA
    cC
    rexcom
    rexbii
    @2
    vy
    vz
    cB
    cC
    rexcom
    3bitri
end
