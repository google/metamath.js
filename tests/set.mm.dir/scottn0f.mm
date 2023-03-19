include "c0.mm"
include "cv.mm"
include "crnk.mm"
include "cfv.mm"
include "wss.mm"
include "wral.mm"
include "crab.mm"
include "scott0f.mm"
include "necon3bii.mm"

theorem scottn0f
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume scottn0f.1: |- F/_ y A
  assume scottn0f.2: |- F/_ x A

  disjoint x y
  assert |- ( A =/= (/) <-> { x e. A | A. y e. A ( rank ` x ) C_ ( rank ` y ) } =/= (/) )

  proof
    cA
    c0
    vx
    cv
    crnk
    cfv
    vy
    cv
    crnk
    cfv
    wss
    vy
    cA
    wral
    vx
    cA
    crab
    c0
    vx
    vy
    cA
    scottn0f.1
    scottn0f.2
    scott0f
    necon3bii
end
