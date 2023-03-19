include "cuni.mm"
include "wrel.mm"
include "cv.mm"
include "ciun.mm"
include "wral.mm"
include "uniiun.mm"
include "releqi.mm"
include "reliun.mm"
include "bitri.mm"

theorem reluni
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( Rel U. A <-> A. x e. A Rel x )

  proof
    cA
    cuni
    #
    wrel
    vx
    cA
    vx
    cv
    #
    ciun
    #
    wrel
    @1
    wrel
    vx
    cA
    wral
    @0
    @2
    vx
    cA
    uniiun
    releqi
    vx
    cA
    @1
    reliun
    bitri
end
