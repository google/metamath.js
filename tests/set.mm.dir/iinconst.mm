include "c0.mm"
include "wne.mm"
include "ciin.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "r19.3rzv.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "syl6rbbr.mm"
include "eqrdv.mm"

theorem iinconst
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A =/= (/) -> |^|_ x e. A B = B )

  proof
    cA
    c0
    wne
    #
    vy
    vx
    cA
    cB
    ciin
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
    wral
    #
    @2
    @1
    wcel
    #
    @3
    vx
    cA
    r19.3rzv
    @2
    cvv
    wcel
    @5
    @4
    wb
    vy
    vex
    vx
    @2
    cA
    cB
    cvv
    eliin
    ax-mp
    syl6rbbr
    eqrdv
end
