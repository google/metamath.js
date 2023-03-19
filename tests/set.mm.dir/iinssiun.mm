include "c0.mm"
include "wne.mm"
include "ciin.mm"
include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wrex.mm"
include "r19.2z.mm"
include "ex.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "eliun.mm"
include "3imtr4g.mm"
include "ssrdv.mm"

theorem iinssiun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  assert |- ( A =/= (/) -> |^|_ x e. A B C_ U_ x e. A B )

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
    vx
    cA
    cB
    ciun
    #
    @0
    vy
    cv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    #
    @4
    vx
    cA
    wrex
    #
    @3
    @1
    wcel
    #
    @3
    @2
    wcel
    @0
    @5
    @6
    @4
    vx
    cA
    r19.2z
    ex
    @3
    cvv
    wcel
    @7
    @5
    wb
    vy
    vex
    vx
    @3
    cA
    cB
    cvv
    eliin
    ax-mp
    vx
    @3
    cA
    cB
    eliun
    3imtr4g
    ssrdv
end
