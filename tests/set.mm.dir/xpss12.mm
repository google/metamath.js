include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "copab.mm"
include "cxp.mm"
include "ssel.mm"
include "im2anan9.mm"
include "ssopab2dv.mm"
include "df-xp.mm"
include "3sstr4g.mm"

theorem xpss12
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A C_ B /\ C C_ D ) -> ( A X. C ) C_ ( B X. D ) )

  proof
    cA
    cB
    wss
    #
    cC
    cD
    wss
    #
    wa
    #
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cC
    wcel
    #
    wa
    #
    vx
    vy
    copab
    @3
    cB
    wcel
    #
    @5
    cD
    wcel
    #
    wa
    #
    vx
    vy
    copab
    cA
    cC
    cxp
    cB
    cD
    cxp
    @2
    @7
    @10
    vx
    vy
    @0
    @4
    @8
    @1
    @6
    @9
    cA
    cB
    @3
    ssel
    cC
    cD
    @5
    ssel
    im2anan9
    ssopab2dv
    vx
    vy
    cA
    cC
    df-xp
    vx
    vy
    cB
    cD
    df-xp
    3sstr4g
end
