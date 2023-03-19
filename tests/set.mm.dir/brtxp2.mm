include "ctxp.mm"
include "wbr.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "w3a.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "txpss3v.mm"
include "brel.mm"
include "simprd.mm"
include "elvv.mm"
include "sylib.mm"
include "pm4.71ri.mm"
include "19.41vv.mm"
include "bitr4i.mm"
include "breq2.mm"
include "pm5.32i.mm"
include "2exbii.mm"
include "vex.mm"
include "brtxp.mm"
include "anbi2i.mm"
include "3anass.mm"
include "3bitri.mm"

theorem brtxp2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  assume brtxp2.1: |- A e. _V

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  assert |- ( A ( R (x) S ) B <-> E. x E. y ( B = <. x , y >. /\ A R x /\ A S y ) )

  proof
    cA
    cB
    cR
    cS
    ctxp
    #
    wbr
    #
    cB
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    @1
    wa
    #
    vy
    wex
    vx
    wex
    #
    @5
    cA
    @4
    @0
    wbr
    #
    wa
    #
    vy
    wex
    vx
    wex
    @5
    cA
    @2
    cR
    wbr
    #
    cA
    @3
    cS
    wbr
    #
    w3a
    #
    vy
    wex
    vx
    wex
    @1
    @5
    vy
    wex
    vx
    wex
    #
    @1
    wa
    @7
    @1
    @13
    @1
    cB
    cvv
    cvv
    cxp
    #
    wcel
    #
    @13
    @1
    cA
    cvv
    wcel
    @15
    cA
    cB
    cvv
    @14
    @0
    cR
    cS
    txpss3v
    brel
    simprd
    vx
    vy
    cB
    elvv
    sylib
    pm4.71ri
    @5
    @1
    vx
    vy
    19.41vv
    bitr4i
    @6
    @9
    vx
    vy
    @5
    @1
    @8
    cB
    @4
    cA
    @0
    breq2
    pm5.32i
    2exbii
    @9
    @12
    vx
    vy
    @9
    @5
    @10
    @11
    wa
    #
    wa
    @12
    @8
    @16
    @5
    cR
    cS
    cA
    @2
    @3
    brtxp2.1
    vx
    vex
    vy
    vex
    brtxp
    anbi2i
    @5
    @10
    @11
    3anass
    bitr4i
    2exbii
    3bitri
end
