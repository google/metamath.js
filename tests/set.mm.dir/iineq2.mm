include "wceq.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "cab.mm"
include "ciin.mm"
include "wb.mm"
include "eleq2.mm"
include "ralimi.mm"
include "ralbi.mm"
include "syl.mm"
include "abbidv.mm"
include "df-iin.mm"
include "3eqtr4g.mm"

theorem iineq2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y


  assert |- ( A. x e. A B = C -> |^|_ x e. A B = |^|_ x e. A C )

  proof
    cB
    cC
    wceq
    #
    vx
    cA
    wral
    #
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
    vy
    cab
    @2
    cC
    wcel
    #
    vx
    cA
    wral
    #
    vy
    cab
    vx
    cA
    cB
    ciin
    vx
    cA
    cC
    ciin
    @1
    @4
    @6
    vy
    @1
    @3
    @5
    wb
    #
    vx
    cA
    wral
    @4
    @6
    wb
    @0
    @7
    vx
    cA
    cB
    cC
    @2
    eleq2
    ralimi
    @3
    @5
    vx
    cA
    ralbi
    syl
    abbidv
    vx
    vy
    cA
    cB
    df-iin
    vx
    vy
    cA
    cC
    df-iin
    3eqtr4g
end
