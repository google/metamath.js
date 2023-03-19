include "cv.mm"
include "wcel.mm"
include "biid.mm"
include "abbi2i.mm"

theorem abid1
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- A = { x | x e. A }

  proof
    vx
    cv
    cA
    wcel
    #
    vx
    cA
    @0
    biid
    abbi2i
end
