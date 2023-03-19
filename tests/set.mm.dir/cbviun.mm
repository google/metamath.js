include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "cab.mm"
include "ciun.mm"
include "nfcri.mm"
include "weq.mm"
include "eleq2d.mm"
include "cbvrex.mm"
include "abbii.mm"
include "df-iun.mm"
include "3eqtr4i.mm"

theorem cbviun
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z
  assume cbviun.1: |- F/_ y B
  assume cbviun.2: |- F/_ x C
  assume cbviun.3: |- ( x = y -> B = C )

  disjoint A y
  disjoint A x
  disjoint y z
  disjoint A z
  disjoint x z
  disjoint B z
  disjoint C z
  assert |- U_ x e. A B = U_ y e. A C

  proof
    vz
    cv
    #
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    vz
    cab
    @0
    cC
    wcel
    #
    vy
    cA
    wrex
    #
    vz
    cab
    vx
    cA
    cB
    ciun
    vy
    cA
    cC
    ciun
    @2
    @4
    vz
    @1
    @3
    vx
    vy
    cA
    vy
    vz
    cB
    cbviun.1
    nfcri
    vx
    vz
    cC
    cbviun.2
    nfcri
    vx
    vy
    weq
    cB
    cC
    @0
    cbviun.3
    eleq2d
    cbvrex
    abbii
    vx
    vz
    cA
    cB
    df-iun
    vy
    vz
    cA
    cC
    df-iun
    3eqtr4i
end
