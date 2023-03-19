include "chil.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "chssii.mm"
include "ocval.mm"
include "ax-mp.mm"

theorem chocvali
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume chocval.1: |- A e. CH

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( _|_ ` A ) = { x e. ~H | A. y e. A ( x .ih y ) = 0 }

  proof
    cA
    chil
    wss
    cA
    cort
    cfv
    vx
    cv
    vy
    cv
    csp
    co
    cc0
    wceq
    vy
    cA
    wral
    vx
    chil
    crab
    wceq
    cA
    chocval.1
    chssii
    vx
    vy
    cA
    ocval
    ax-mp
end
