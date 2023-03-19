include "wss.mm"
include "ciin.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "ssralv.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "3imtr4g.mm"
include "ssrdv.mm"

theorem iinss1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  assert |- ( A C_ B -> |^|_ x e. B C C_ |^|_ x e. A C )

  proof
    cA
    cB
    wss
    #
    vy
    vx
    cB
    cC
    ciin
    #
    vx
    cA
    cC
    ciin
    #
    @0
    vy
    cv
    #
    cC
    wcel
    #
    vx
    cB
    wral
    #
    @4
    vx
    cA
    wral
    #
    @3
    @1
    wcel
    #
    @3
    @2
    wcel
    #
    @4
    vx
    cA
    cB
    ssralv
    @3
    cvv
    wcel
    #
    @7
    @5
    wb
    vy
    vex
    #
    vx
    @3
    cB
    cC
    cvv
    eliin
    ax-mp
    @9
    @8
    @6
    wb
    @10
    vx
    @3
    cA
    cC
    cvv
    eliin
    ax-mp
    3imtr4g
    ssrdv
end
