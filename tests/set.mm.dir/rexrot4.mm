include "wrex.mm"
include "rexcom13.mm"
include "rexbii.mm"
include "bitri.mm"

theorem rexrot4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D

  disjoint w z
  disjoint A w
  disjoint A z
  disjoint B w
  disjoint B z
  disjoint w x
  disjoint w y
  disjoint C w
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  assert |- ( E. x e. A E. y e. B E. z e. C E. w e. D ph <-> E. z e. C E. w e. D E. x e. A E. y e. B ph )

  proof
    wph
    vw
    cD
    wrex
    vz
    cC
    wrex
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    wph
    vy
    cB
    wrex
    #
    vz
    cC
    wrex
    vw
    cD
    wrex
    #
    vx
    cA
    wrex
    @1
    vx
    cA
    wrex
    vw
    cD
    wrex
    vz
    cC
    wrex
    @0
    @2
    vx
    cA
    wph
    vy
    vz
    vw
    cB
    cC
    cD
    rexcom13
    rexbii
    @1
    vx
    vw
    vz
    cA
    cD
    cC
    rexcom13
    bitri
end
