include "wcel.mm"
include "wse.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cpred.mm"
include "cvv.mm"
include "wceq.mm"
include "cab.mm"
include "vex.mm"
include "elpred.mm"
include "abbi2dv.mm"
include "df-rab.mm"
include "syl6reqr.mm"
include "adantr.mm"
include "seex.mm"
include "ancoms.mm"
include "eqeltrrd.mm"

theorem setlikespec
  let cA: class A
  let cR: class R
  let cX: class X
  let vx: setvar x


  assert |- ( ( X e. A /\ R Se A ) -> Pred ( R , A , X ) e. _V )

  proof
    cX
    cA
    wcel
    #
    cA
    cR
    wse
    #
    wa
    vx
    cv
    #
    cX
    cR
    wbr
    #
    vx
    cA
    crab
    #
    cA
    cR
    cX
    cpred
    #
    cvv
    @0
    @4
    @5
    wceq
    @1
    @0
    @5
    @2
    cA
    wcel
    @3
    wa
    #
    vx
    cab
    @4
    @0
    @6
    vx
    @5
    cA
    cA
    cR
    cX
    @2
    vx
    vex
    elpred
    abbi2dv
    @3
    vx
    cA
    df-rab
    syl6reqr
    adantr
    @1
    @0
    @4
    cvv
    wcel
    vx
    cA
    cX
    cR
    seex
    ancoms
    eqeltrrd
end
