include "cv.mm"
include "wcel.mm"
include "cab.mm"
include "biid.mm"
include "bj-abbi2i.mm"
include "eqcomi.mm"

theorem bj-abid2
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- { x | x e. A } = A

  proof
    cA
    vx
    cv
    cA
    wcel
    #
    vx
    cab
    @0
    vx
    cA
    @0
    biid
    bj-abbi2i
    eqcomi
end
