include "cv.mm"
include "wcel.mm"
include "biid.mm"
include "bj-abbi2i.mm"

theorem bj-termab
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
    bj-abbi2i
end
