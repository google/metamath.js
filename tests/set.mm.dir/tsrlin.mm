include "ctsr.mm"
include "wcel.mm"
include "wbr.mm"
include "wo.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cps.mm"
include "istsr2.mm"
include "simprbi.mm"
include "wceq.mm"
include "breq1.mm"
include "breq2.mm"
include "orbi12d.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"

theorem tsrlin
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  assume istsr.1: |- X = dom R


  assert |- ( ( R e. TosetRel /\ A e. X /\ B e. X ) -> ( A R B \/ B R A ) )

  proof
    cR
    ctsr
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cA
    cB
    cR
    wbr
    #
    cB
    cA
    cR
    wbr
    #
    wo
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @7
    @6
    cR
    wbr
    #
    wo
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @1
    @2
    wa
    @5
    @0
    cR
    cps
    wcel
    @11
    vx
    vy
    cR
    cX
    istsr.1
    istsr2
    simprbi
    @10
    @5
    cA
    @7
    cR
    wbr
    #
    @7
    cA
    cR
    wbr
    #
    wo
    vx
    vy
    cA
    cB
    cX
    cX
    @6
    cA
    wceq
    @8
    @12
    @9
    @13
    @6
    cA
    @7
    cR
    breq1
    @6
    cA
    @7
    cR
    breq2
    orbi12d
    @7
    cB
    wceq
    @12
    @3
    @13
    @4
    @7
    cB
    cA
    cR
    breq2
    @7
    cB
    cA
    cR
    breq1
    orbi12d
    rspc2v
    syl5com
    3impib
end
