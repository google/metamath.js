include "wrel.mm"
include "wcel.mm"
include "cint.mm"
include "cdm.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wi.mm"
include "df-rel.mm"
include "ssel.mm"
include "sylbi.mm"
include "elvv.mm"
include "syl6ib.mm"
include "eleq1.mm"
include "vex.mm"
include "opeldm.mm"
include "syl6bi.mm"
include "inteq.mm"
include "inteqd.mm"
include "op1stb.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "sylibrd.mm"
include "exlimivv.mm"
include "syli.mm"
include "imp.mm"

theorem elreldm
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( Rel A /\ B e. A ) -> |^| |^| B e. dom A )

  proof
    cA
    wrel
    #
    cB
    cA
    wcel
    #
    cB
    cint
    #
    cint
    #
    cA
    cdm
    #
    wcel
    #
    @1
    @0
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
    vy
    wex
    vx
    wex
    #
    @5
    @0
    @1
    cB
    cvv
    cvv
    cxp
    #
    wcel
    #
    @10
    @0
    cA
    @11
    wss
    @1
    @12
    wi
    cA
    df-rel
    cA
    @11
    cB
    ssel
    sylbi
    vx
    vy
    cB
    elvv
    syl6ib
    @9
    @1
    @5
    wi
    vx
    vy
    @9
    @1
    @6
    @4
    wcel
    #
    @5
    @9
    @1
    @8
    cA
    wcel
    @13
    cB
    @8
    cA
    eleq1
    @6
    @7
    cA
    vx
    vex
    #
    vy
    vex
    #
    opeldm
    syl6bi
    @9
    @3
    @6
    @4
    @9
    @3
    @8
    cint
    #
    cint
    @6
    @9
    @2
    @16
    cB
    @8
    inteq
    inteqd
    @6
    @7
    @14
    @15
    op1stb
    syl6eq
    eleq1d
    sylibrd
    exlimivv
    syli
    imp
end
