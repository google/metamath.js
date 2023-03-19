include "c0.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wn.mm"
include "wal.mm"
include "risset.mm"
include "eq0.mm"
include "rexbii.mm"
include "bitri.mm"

theorem 0el
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint A x
  disjoint x y
  assert |- ( (/) e. A <-> E. x e. A A. y -. y e. x )

  proof
    c0
    cA
    wcel
    vx
    cv
    #
    c0
    wceq
    #
    vx
    cA
    wrex
    vy
    cv
    @0
    wcel
    wn
    vy
    wal
    #
    vx
    cA
    wrex
    vx
    c0
    cA
    risset
    @1
    @2
    vx
    cA
    vy
    @0
    eq0
    rexbii
    bitri
end
