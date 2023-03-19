include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "cab.mm"
include "ciun.mm"
include "nfcri.mm"
include "weq.mm"
include "eleq2d.mm"
include "cbvrexf.mm"
include "abbii.mm"
include "df-iun.mm"
include "3eqtr4i.mm"

theorem cbviunf
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z
  assume cbviunf.x: |- F/_ x A
  assume cbviunf.y: |- F/_ y A
  assume cbviunf.1: |- F/_ y B
  assume cbviunf.2: |- F/_ x C
  assume cbviunf.3: |- ( x = y -> B = C )

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A z
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
    cbviunf.x
    cbviunf.y
    vy
    vz
    cB
    cbviunf.1
    nfcri
    vx
    vz
    cC
    cbviunf.2
    nfcri
    vx
    vy
    weq
    cB
    cC
    @0
    cbviunf.3
    eleq2d
    cbvrexf
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
