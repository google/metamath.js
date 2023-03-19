include "c0.mm"
include "wne.mm"
include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "r19.9rzv.mm"
include "eliun.mm"
include "syl6rbbr.mm"
include "eqrdv.mm"

theorem iunconst
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A =/= (/) -> U_ x e. A B = B )

  proof
    cA
    c0
    wne
    #
    vy
    vx
    cA
    cB
    ciun
    #
    cB
    @0
    vy
    cv
    #
    cB
    wcel
    #
    @3
    vx
    cA
    wrex
    @2
    @1
    wcel
    @3
    vx
    cA
    r19.9rzv
    vx
    @2
    cA
    cB
    eliun
    syl6rbbr
    eqrdv
end
