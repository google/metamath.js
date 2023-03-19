include "cv.mm"
include "wceq.mm"
include "copab.mm"
include "wfun.mm"
include "wmo.mm"
include "funopab.mm"
include "moeq.mm"
include "mpgbir.mm"

theorem funopabeq
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A y
  assert |- Fun { <. x , y >. | y = A }

  proof
    vy
    cv
    cA
    wceq
    #
    vx
    vy
    copab
    wfun
    @0
    vy
    wmo
    vx
    @0
    vx
    vy
    funopab
    vy
    cA
    moeq
    mpgbir
end
