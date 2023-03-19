include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "bj-elissetv.mm"
include "bj-denotes.mm"
include "sylib.mm"

theorem bj-elisset
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint A y
  disjoint V y
  assert |- ( A e. V -> E. x x = A )

  proof
    cA
    cV
    wcel
    vy
    cv
    cA
    wceq
    vy
    wex
    vx
    cv
    cA
    wceq
    vx
    wex
    vy
    cA
    cV
    bj-elissetv
    vy
    vx
    cA
    bj-denotes
    sylib
end
