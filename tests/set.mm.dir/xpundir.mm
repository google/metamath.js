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
include "anbi1i.mm"
include "andir.mm"
include "bitri.mm"
include "opabbii.mm"
include "unopab.mm"
include "eqtr4i.mm"

theorem xpundir
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A u. B ) X. C ) = ( ( A X. C ) u. ( B X. C ) )

  proof
    cA
    cB
    cun
    #
    cC
    cxp
    vx
    cv
    #
    @0
    wcel
    #
    vy
    cv
    cC
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    cA
    cC
    cxp
    #
    cB
    cC
    cxp
    #
    cun
    #
    vx
    vy
    @0
    cC
    df-xp
    @8
    @1
    cA
    wcel
    #
    @3
    wa
    #
    vx
    vy
    copab
    #
    @1
    cB
    wcel
    #
    @3
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
    cC
    df-xp
    vx
    vy
    cB
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
    @9
    @12
    wo
    #
    @3
    wa
    @16
    @2
    @17
    @3
    @1
    cA
    cB
    elun
    anbi1i
    @9
    @12
    @3
    andir
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
