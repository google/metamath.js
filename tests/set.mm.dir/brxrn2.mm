include "cxrn.mm"
include "wbr.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wcel.mm"
include "w3a.mm"
include "cvv.mm"
include "cxp.mm"
include "xrnss3v.mm"
include "brel.mm"
include "simprd.mm"
include "elvv.mm"
include "sylib.mm"
include "pm4.71ri.mm"
include "19.41vv.mm"
include "breq2.mm"
include "pm5.32i.mm"
include "2exbii.mm"
include "3bitr2i.mm"
include "wb.mm"
include "brxrn.mm"
include "el3v23.mm"
include "anbi2d.mm"
include "3anass.mm"
include "syl6bbr.mm"
include "2exbidv.mm"
include "syl5bb.mm"

theorem brxrn2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cV: class V

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint V x
  disjoint V y
  assert |- ( A e. V -> ( A ( R |X. S ) B <-> E. x E. y ( B = <. x , y >. /\ A R x /\ A S y ) ) )

  proof
    cA
    cB
    cR
    cS
    cxrn
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
    #
    cA
    cV
    wcel
    #
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
    @5
    @1
    wa
    #
    vy
    wex
    vx
    wex
    @8
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
    @16
    cA
    cB
    cvv
    @15
    @0
    cR
    cS
    xrnss3v
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
    @14
    @7
    vx
    vy
    @5
    @1
    @6
    cB
    @4
    cA
    @0
    breq2
    pm5.32i
    2exbii
    3bitr2i
    @9
    @7
    @12
    vx
    vy
    @9
    @7
    @5
    @10
    @11
    wa
    #
    wa
    @12
    @9
    @6
    @17
    @5
    @9
    @6
    @17
    wb
    vx
    vy
    cA
    @2
    @3
    cR
    cS
    cV
    cvv
    cvv
    brxrn
    el3v23
    anbi2d
    @5
    @10
    @11
    3anass
    syl6bbr
    2exbidv
    syl5bb
end
