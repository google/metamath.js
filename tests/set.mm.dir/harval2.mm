include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "char.mm"
include "cfv.mm"
include "cv.mm"
include "csdm.mm"
include "wbr.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "wss.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "cdom.mm"
include "wceq.mm"
include "harval.mm"
include "adantr.mm"
include "domsdomtr.mm"
include "sdomel.mm"
include "syl5.mm"
include "imp.mm"
include "an4s.mm"
include "ancoms.mm"
include "3impb.mm"
include "rabssdv.mm"
include "adantl.mm"
include "eqsstrd.mm"
include "expr.mm"
include "ralrimiva.mm"
include "ssintrab.mm"
include "sylibr.mm"
include "harcl.mm"
include "a1i.mm"
include "harsdom.mm"
include "breq2.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "intss1.mm"
include "syl.mm"
include "eqssd.mm"

theorem harval2
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A e. dom card -> ( har ` A ) = |^| { x e. On | A ~< x } )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    cA
    char
    cfv
    #
    cA
    vx
    cv
    #
    csdm
    wbr
    #
    vx
    con0
    crab
    #
    cint
    #
    @1
    @4
    @2
    @3
    wss
    #
    wi
    #
    vx
    con0
    wral
    @2
    @6
    wss
    @1
    @8
    vx
    con0
    @1
    @3
    con0
    wcel
    #
    @4
    @7
    @1
    @9
    @4
    wa
    #
    wa
    @2
    vy
    cv
    #
    cA
    cdom
    wbr
    #
    vy
    con0
    crab
    #
    @3
    @1
    @2
    @13
    wceq
    @10
    vy
    @0
    cA
    harval
    adantr
    @10
    @13
    @3
    wss
    @1
    @10
    @12
    vy
    con0
    @3
    @10
    @11
    con0
    wcel
    #
    @12
    @11
    @3
    wcel
    #
    @14
    @12
    wa
    @10
    @15
    @14
    @9
    @12
    @4
    @15
    @14
    @9
    wa
    #
    @12
    @4
    wa
    #
    @15
    @17
    @11
    @3
    csdm
    wbr
    @16
    @15
    @11
    cA
    @3
    domsdomtr
    @11
    @3
    sdomel
    syl5
    imp
    an4s
    ancoms
    3impb
    rabssdv
    adantl
    eqsstrd
    expr
    ralrimiva
    @4
    vx
    @2
    con0
    ssintrab
    sylibr
    @1
    @2
    @5
    wcel
    #
    @6
    @2
    wss
    @1
    @2
    con0
    wcel
    #
    cA
    @2
    csdm
    wbr
    #
    @18
    @19
    @1
    cA
    harcl
    a1i
    cA
    harsdom
    @4
    @20
    vx
    @2
    con0
    @3
    @2
    cA
    csdm
    breq2
    elrab
    sylanbrc
    @2
    @5
    intss1
    syl
    eqssd
end
