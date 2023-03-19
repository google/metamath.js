include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "cab.mm"
include "ciin.mm"
include "nfcri.mm"
include "weq.mm"
include "eleq2d.mm"
include "cbvral.mm"
include "abbii.mm"
include "df-iin.mm"
include "3eqtr4i.mm"

theorem cbviin
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
  assert |- |^|_ x e. A B = |^|_ y e. A C

  proof
    vz
    cv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    #
    vz
    cab
    @0
    cC
    wcel
    #
    vy
    cA
    wral
    #
    vz
    cab
    vx
    cA
    cB
    ciin
    vy
    cA
    cC
    ciin
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
    cbvral
    abbii
    vx
    vz
    cA
    cB
    df-iin
    vy
    vz
    cA
    cC
    df-iin
    3eqtr4i
end
