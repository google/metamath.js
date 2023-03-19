include "wss.mm"
include "wrex.mm"
include "ciin.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "wi.mm"
include "ssel.mm"
include "reximi.mm"
include "r19.36v.mm"
include "syl.mm"
include "syl5bi.mm"
include "ssrdv.mm"

theorem iinss
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint C x
  disjoint x y
  disjoint C y
  disjoint A y
  disjoint B y
  assert |- ( E. x e. A B C_ C -> |^|_ x e. A B C_ C )

  proof
    cB
    cC
    wss
    #
    vx
    cA
    wrex
    #
    vy
    vx
    cA
    cB
    ciin
    #
    cC
    vy
    cv
    #
    @2
    wcel
    #
    @3
    cB
    wcel
    #
    vx
    cA
    wral
    #
    @1
    @3
    cC
    wcel
    #
    @3
    cvv
    wcel
    @4
    @6
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
    @1
    @5
    @7
    wi
    #
    vx
    cA
    wrex
    @6
    @7
    wi
    @0
    @8
    vx
    cA
    cB
    cC
    @3
    ssel
    reximi
    @5
    @7
    vx
    cA
    r19.36v
    syl
    syl5bi
    ssrdv
end
