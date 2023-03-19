include "ciun.mm"
include "ccnv.mm"
include "relcnv.mm"
include "wrel.mm"
include "reliun.mm"
include "cv.mm"
include "wcel.mm"
include "a1i.mm"
include "mprgbir.mm"
include "cop.mm"
include "wrex.mm"
include "vex.mm"
include "opelcnv.mm"
include "bicomi.mm"
include "rexbii.mm"
include "eliun.mm"
include "bitri.mm"
include "3bitr4i.mm"
include "eqrelriiv.mm"

theorem cnviun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  assert |- `' U_ x e. A B = U_ x e. A `' B

  proof
    vy
    vz
    vx
    cA
    cB
    ciun
    #
    ccnv
    #
    vx
    cA
    cB
    ccnv
    #
    ciun
    #
    @0
    relcnv
    @3
    wrel
    @2
    wrel
    #
    vx
    cA
    vx
    cA
    @2
    reliun
    @4
    vx
    cv
    cA
    wcel
    cB
    relcnv
    a1i
    mprgbir
    vz
    cv
    #
    vy
    cv
    #
    cop
    #
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    @6
    @5
    cop
    #
    @2
    wcel
    #
    vx
    cA
    wrex
    @10
    @1
    wcel
    #
    @10
    @3
    wcel
    @8
    @11
    vx
    cA
    @11
    @8
    @6
    @5
    cB
    vy
    vex
    #
    vz
    vex
    #
    opelcnv
    bicomi
    rexbii
    @12
    @7
    @0
    wcel
    @9
    @6
    @5
    @0
    @13
    @14
    opelcnv
    vx
    @7
    cA
    cB
    eliun
    bitri
    vx
    @10
    cA
    @2
    eliun
    3bitr4i
    eqrelriiv
end
