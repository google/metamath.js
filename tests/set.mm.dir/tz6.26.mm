include "wwe.mm"
include "wse.mm"
include "wa.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "cpred.mm"
include "wceq.mm"
include "wreu.mm"
include "wereu2.mm"
include "reurex.mm"
include "syl.mm"
include "crab.mm"
include "rabeq0.mm"
include "cab.mm"
include "cin.mm"
include "dfrab3.mm"
include "vex.mm"
include "dfpred2.mm"
include "eqtr4i.mm"
include "eqeq1i.mm"
include "bitr3i.mm"
include "rexbii.mm"
include "sylib.mm"

theorem tz6.26
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let vx: setvar x

  disjoint A y
  disjoint B y
  disjoint R y
  disjoint x y
  disjoint A x
  disjoint B x
  disjoint R x
  assert |- ( ( ( R We A /\ R Se A ) /\ ( B C_ A /\ B =/= (/) ) ) -> E. y e. B Pred ( R , B , y ) = (/) )

  proof
    cA
    cR
    wwe
    cA
    cR
    wse
    wa
    cB
    cA
    wss
    cB
    c0
    wne
    wa
    wa
    #
    vx
    cv
    vy
    cv
    #
    cR
    wbr
    #
    wn
    vx
    cB
    wral
    #
    vy
    cB
    wrex
    #
    cB
    cR
    @1
    cpred
    #
    c0
    wceq
    #
    vy
    cB
    wrex
    @0
    @3
    vy
    cB
    wreu
    @4
    vy
    vx
    cA
    cB
    cR
    wereu2
    @3
    vy
    cB
    reurex
    syl
    @3
    @6
    vy
    cB
    @3
    @2
    vx
    cB
    crab
    #
    c0
    wceq
    @6
    @2
    vx
    cB
    rabeq0
    @7
    @5
    c0
    @7
    cB
    @2
    vx
    cab
    cin
    @5
    @2
    vx
    cB
    dfrab3
    vx
    cB
    cR
    @1
    vy
    vex
    dfpred2
    eqtr4i
    eqeq1i
    bitr3i
    rexbii
    sylib
end
