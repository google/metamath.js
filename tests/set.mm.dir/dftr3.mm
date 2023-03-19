include "wtr.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "dftr5.mm"
include "dfss3.mm"
include "ralbii.mm"
include "bitr4i.mm"

theorem dftr3
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( Tr A <-> A. x e. A x C_ A )

  proof
    cA
    wtr
    vy
    cv
    cA
    wcel
    vy
    vx
    cv
    #
    wral
    #
    vx
    cA
    wral
    @0
    cA
    wss
    #
    vx
    cA
    wral
    vx
    vy
    cA
    dftr5
    @2
    @1
    vx
    cA
    vy
    @0
    cA
    dfss3
    ralbii
    bitr4i
end
