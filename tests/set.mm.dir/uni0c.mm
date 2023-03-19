include "cuni.mm"
include "c0.mm"
include "wceq.mm"
include "csn.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "uni0b.mm"
include "dfss3.mm"
include "velsn.mm"
include "ralbii.mm"
include "3bitri.mm"

theorem uni0c
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( U. A = (/) <-> A. x e. A x = (/) )

  proof
    cA
    cuni
    c0
    wceq
    cA
    c0
    csn
    #
    wss
    vx
    cv
    #
    @0
    wcel
    #
    vx
    cA
    wral
    @1
    c0
    wceq
    #
    vx
    cA
    wral
    cA
    uni0b
    vx
    cA
    @0
    dfss3
    @2
    @3
    vx
    cA
    vx
    c0
    velsn
    ralbii
    3bitri
end
