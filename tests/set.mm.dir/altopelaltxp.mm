include "caltop.mm"
include "caltxp.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "elaltxp.mm"
include "reeanv.mm"
include "eqcom.mm"
include "vex.mm"
include "altopth.mm"
include "bitri.mm"
include "2rexbii.mm"
include "risset.mm"
include "anbi12i.mm"
include "3bitr4i.mm"

theorem altopelaltxp
  let cA: class A
  let cB: class B
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y


  assert |- ( << X , Y >> e. ( A XX. B ) <-> ( X e. A /\ Y e. B ) )

  proof
    cX
    cY
    caltop
    #
    cA
    cB
    caltxp
    wcel
    @0
    vx
    cv
    #
    vy
    cv
    #
    caltop
    #
    wceq
    #
    vy
    cB
    wrex
    vx
    cA
    wrex
    #
    cX
    cA
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    vx
    vy
    cA
    cB
    @0
    elaltxp
    @1
    cX
    wceq
    #
    @2
    cY
    wceq
    #
    wa
    #
    vy
    cB
    wrex
    vx
    cA
    wrex
    @9
    vx
    cA
    wrex
    #
    @10
    vy
    cB
    wrex
    #
    wa
    @5
    @8
    @9
    @10
    vx
    vy
    cA
    cB
    reeanv
    @4
    @11
    vx
    vy
    cA
    cB
    @4
    @3
    @0
    wceq
    @11
    @0
    @3
    eqcom
    @1
    @2
    cX
    cY
    vx
    vex
    vy
    vex
    altopth
    bitri
    2rexbii
    @6
    @12
    @7
    @13
    vx
    cX
    cA
    risset
    vy
    cY
    cB
    risset
    anbi12i
    3bitr4i
    bitri
end
