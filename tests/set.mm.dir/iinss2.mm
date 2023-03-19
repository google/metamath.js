include "cv.mm"
include "wcel.mm"
include "ciin.mm"
include "wral.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "rsp.mm"
include "com12.mm"
include "syl5bi.mm"
include "ssrdv.mm"

theorem iinss2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y


  assert |- ( x e. A -> |^|_ x e. A B C_ B )

  proof
    vx
    cv
    cA
    wcel
    #
    vy
    vx
    cA
    cB
    ciin
    #
    cB
    vy
    cv
    #
    @1
    wcel
    #
    @2
    cB
    wcel
    #
    vx
    cA
    wral
    #
    @0
    @4
    @2
    cvv
    wcel
    @3
    @5
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
    @5
    @0
    @4
    @4
    vx
    cA
    rsp
    com12
    syl5bi
    ssrdv
end
