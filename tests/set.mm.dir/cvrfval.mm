include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wa.mm"
include "wbr.mm"
include "wrex.mm"
include "wn.mm"
include "w3a.mm"
include "copab.mm"
include "wceq.mm"
include "elex.mm"
include "ccvr.mm"
include "cfv.mm"
include "cbs.mm"
include "cplt.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "breqd.mm"
include "rexeqbidv.mm"
include "notbid.mm"
include "3anbi123d.mm"
include "opabbidv.mm"
include "df-covers.mm"
include "3anass.mm"
include "opabbii.mm"
include "cxp.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "opabssxp.mm"
include "ssexi.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem cvrfval
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let c.lt: class .<
  let cK: class K
  let vp: setvar p
  assume cvrfval.b: |- B = ( Base ` K )
  assume cvrfval.s: |- .< = ( lt ` K )
  assume cvrfval.c: |- C = ( <o ` K )

  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint B p
  disjoint K p
  disjoint .< p
  assert |- ( K e. A -> C = { <. x , y >. | ( ( x e. B /\ y e. B ) /\ x .< y /\ -. E. z e. B ( x .< z /\ z .< y ) ) } )

  proof
    cK
    cA
    wcel
    cK
    cvv
    wcel
    #
    cC
    vx
    cv
    #
    cB
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    @1
    @3
    c.lt
    wbr
    #
    @1
    vz
    cv
    #
    c.lt
    wbr
    #
    @7
    @3
    c.lt
    wbr
    #
    wa
    #
    vz
    cB
    wrex
    #
    wn
    #
    w3a
    #
    vx
    vy
    copab
    #
    wceq
    cK
    cA
    elex
    @0
    cC
    cK
    ccvr
    cfv
    @14
    cvrfval.c
    vp
    cK
    @1
    vp
    cv
    #
    cbs
    cfv
    #
    wcel
    #
    @3
    @16
    wcel
    #
    wa
    #
    @1
    @3
    @15
    cplt
    cfv
    #
    wbr
    #
    @1
    @7
    @20
    wbr
    #
    @7
    @3
    @20
    wbr
    #
    wa
    #
    vz
    @16
    wrex
    #
    wn
    #
    w3a
    #
    vx
    vy
    copab
    @14
    cvv
    ccvr
    @15
    cK
    wceq
    #
    @27
    @13
    vx
    vy
    @28
    @19
    @5
    @21
    @6
    @26
    @12
    @28
    @17
    @2
    @18
    @4
    @28
    @16
    cB
    @1
    @28
    @16
    cK
    cbs
    cfv
    #
    cB
    @15
    cK
    cbs
    fveq2
    cvrfval.b
    syl6eqr
    #
    eleq2d
    @28
    @16
    cB
    @3
    @30
    eleq2d
    anbi12d
    @28
    @20
    c.lt
    @1
    @3
    @28
    @20
    cK
    cplt
    cfv
    c.lt
    @15
    cK
    cplt
    fveq2
    cvrfval.s
    syl6eqr
    #
    breqd
    @28
    @25
    @11
    @28
    @24
    @10
    vz
    @16
    cB
    @30
    @28
    @22
    @8
    @23
    @9
    @28
    @20
    c.lt
    @1
    @7
    @31
    breqd
    @28
    @20
    c.lt
    @7
    @3
    @31
    breqd
    anbi12d
    rexeqbidv
    notbid
    3anbi123d
    opabbidv
    vz
    vp
    vx
    vy
    df-covers
    @14
    @5
    @6
    @12
    wa
    #
    wa
    #
    vx
    vy
    copab
    #
    cvv
    @13
    @33
    vx
    vy
    @5
    @6
    @12
    3anass
    opabbii
    @34
    cB
    cB
    cxp
    cB
    cB
    cB
    @29
    cvv
    cvrfval.b
    cK
    cbs
    fvex
    eqeltri
    #
    @35
    xpex
    @32
    vx
    vy
    cB
    cB
    opabssxp
    ssexi
    eqeltri
    fvmpt
    syl5eq
    syl
end
