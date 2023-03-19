include "cun.mm"
include "cxp.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "df-xp.mm"
include "uneq12i.mm"
include "wo.mm"
include "elun.mm"
include "anbi2i.mm"
include "andi.mm"
include "bitri.mm"
include "opabbii.mm"
include "unopab.mm"
include "eqtr4i.mm"

theorem xpundi
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( A X. ( B u. C ) ) = ( ( A X. B ) u. ( A X. C ) )

  proof
    cA
    cB
    cC
    cun
    #
    cxp
    vx
    cv
    cA
    wcel
    #
    vy
    cv
    #
    @0
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    cA
    cB
    cxp
    #
    cA
    cC
    cxp
    #
    cun
    #
    vx
    vy
    cA
    @0
    df-xp
    @8
    @1
    @2
    cB
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    @1
    @2
    cC
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    cun
    #
    @5
    @6
    @11
    @7
    @14
    vx
    vy
    cA
    cB
    df-xp
    vx
    vy
    cA
    cC
    df-xp
    uneq12i
    @5
    @10
    @13
    wo
    #
    vx
    vy
    copab
    @15
    @4
    @16
    vx
    vy
    @4
    @1
    @9
    @12
    wo
    #
    wa
    @16
    @3
    @17
    @1
    @2
    cB
    cC
    elun
    anbi2i
    @1
    @9
    @12
    andi
    bitri
    opabbii
    @10
    @13
    vx
    vy
    unopab
    eqtr4i
    eqtr4i
    eqtr4i
end
