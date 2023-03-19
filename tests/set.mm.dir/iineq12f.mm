include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "cab.mm"
include "ciin.mm"
include "wb.mm"
include "eleq2.mm"
include "ralimi.mm"
include "ralbi.mm"
include "syl.mm"
include "raleqf.mm"
include "sylan9bbr.mm"
include "abbidv.mm"
include "df-iin.mm"
include "3eqtr4g.mm"

theorem iineq12f
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vy: setvar y
  assume iineq12f.1: |- F/_ x A
  assume iineq12f.2: |- F/_ x B


  assert |- ( ( A = B /\ A. x e. A C = D ) -> |^|_ x e. A C = |^|_ x e. B D )

  proof
    cA
    cB
    wceq
    #
    cC
    cD
    wceq
    #
    vx
    cA
    wral
    #
    wa
    #
    vy
    cv
    #
    cC
    wcel
    #
    vx
    cA
    wral
    #
    vy
    cab
    @4
    cD
    wcel
    #
    vx
    cB
    wral
    #
    vy
    cab
    vx
    cA
    cC
    ciin
    vx
    cB
    cD
    ciin
    @3
    @6
    @8
    vy
    @2
    @6
    @7
    vx
    cA
    wral
    #
    @0
    @8
    @2
    @5
    @7
    wb
    #
    vx
    cA
    wral
    @6
    @9
    wb
    @1
    @10
    vx
    cA
    cC
    cD
    @4
    eleq2
    ralimi
    @5
    @7
    vx
    cA
    ralbi
    syl
    @7
    vx
    cA
    cB
    iineq12f.1
    iineq12f.2
    raleqf
    sylan9bbr
    abbidv
    vx
    vy
    cA
    cC
    df-iin
    vx
    vy
    cB
    cD
    df-iin
    3eqtr4g
end
