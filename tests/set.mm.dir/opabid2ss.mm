include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "id.mm"
include "opabssi.mm"

theorem opabid2ss
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- { <. x , y >. | <. x , y >. e. A } C_ A

  proof
    vx
    cv
    vy
    cv
    cop
    cA
    wcel
    #
    vx
    vy
    cA
    @0
    id
    opabssi
end
