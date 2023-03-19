include "cv.mm"
include "cop.mm"
include "wbr.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "cfv.mm"
include "wceq.mm"
include "c2nd.mm"
include "wo.mm"
include "copab.mm"
include "df-br.mm"
include "eleq2i.mm"
include "bitri.mm"
include "opex.mm"
include "eleq1.mm"
include "opelxp.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "vex.mm"
include "op1std.mm"
include "breq1d.mm"
include "eqeq1d.mm"
include "op2ndd.mm"
include "anbi12d.mm"
include "orbi12d.mm"
include "anbi2d.mm"
include "breq2d.mm"
include "eqeq2d.mm"
include "opelopab.mm"
include "an4.mm"
include "anbi1i.mm"
include "3bitri.mm"

theorem xporderlem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume xporderlem.1: |- T = { <. x , y >. | ( ( x e. ( A X. B ) /\ y e. ( A X. B ) ) /\ ( ( 1st ` x ) R ( 1st ` y ) \/ ( ( 1st ` x ) = ( 1st ` y ) /\ ( 2nd ` x ) S ( 2nd ` y ) ) ) ) }

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint d x
  disjoint d y
  assert |- ( <. a , b >. T <. c , d >. <-> ( ( ( a e. A /\ c e. A ) /\ ( b e. B /\ d e. B ) ) /\ ( a R c \/ ( a = c /\ b S d ) ) ) )

  proof
    va
    cv
    #
    vb
    cv
    #
    cop
    #
    vc
    cv
    #
    vd
    cv
    #
    cop
    #
    cT
    wbr
    #
    @2
    @5
    cop
    #
    vx
    cv
    #
    cA
    cB
    cxp
    #
    wcel
    #
    vy
    cv
    #
    @9
    wcel
    #
    wa
    #
    @8
    c1st
    cfv
    #
    @11
    c1st
    cfv
    #
    cR
    wbr
    #
    @14
    @15
    wceq
    #
    @8
    c2nd
    cfv
    #
    @11
    c2nd
    cfv
    #
    cS
    wbr
    #
    wa
    #
    wo
    #
    wa
    #
    vx
    vy
    copab
    #
    wcel
    #
    @0
    cA
    wcel
    #
    @1
    cB
    wcel
    #
    wa
    #
    @3
    cA
    wcel
    #
    @4
    cB
    wcel
    #
    wa
    #
    wa
    #
    @0
    @3
    cR
    wbr
    #
    @0
    @3
    wceq
    #
    @1
    @4
    cS
    wbr
    #
    wa
    #
    wo
    #
    wa
    #
    @26
    @29
    wa
    @27
    @30
    wa
    wa
    #
    @37
    wa
    @6
    @7
    cT
    wcel
    @25
    @2
    @5
    cT
    df-br
    cT
    @24
    @7
    xporderlem.1
    eleq2i
    bitri
    @23
    @28
    @12
    wa
    #
    @0
    @15
    cR
    wbr
    #
    @0
    @15
    wceq
    #
    @1
    @19
    cS
    wbr
    #
    wa
    #
    wo
    #
    wa
    @38
    vx
    vy
    @2
    @5
    @0
    @1
    opex
    @3
    @4
    opex
    @8
    @2
    wceq
    #
    @13
    @40
    @22
    @45
    @46
    @10
    @28
    @12
    @46
    @10
    @2
    @9
    wcel
    @28
    @8
    @2
    @9
    eleq1
    @0
    @1
    cA
    cB
    opelxp
    syl6bb
    anbi1d
    @46
    @16
    @41
    @21
    @44
    @46
    @14
    @0
    @15
    cR
    @0
    @1
    @8
    va
    vex
    #
    vb
    vex
    #
    op1std
    #
    breq1d
    @46
    @17
    @42
    @20
    @43
    @46
    @14
    @0
    @15
    @49
    eqeq1d
    @46
    @18
    @1
    @19
    cS
    @0
    @1
    @8
    @47
    @48
    op2ndd
    breq1d
    anbi12d
    orbi12d
    anbi12d
    @11
    @5
    wceq
    #
    @40
    @32
    @45
    @37
    @50
    @12
    @31
    @28
    @50
    @12
    @5
    @9
    wcel
    @31
    @11
    @5
    @9
    eleq1
    @3
    @4
    cA
    cB
    opelxp
    syl6bb
    anbi2d
    @50
    @41
    @33
    @44
    @36
    @50
    @15
    @3
    @0
    cR
    @3
    @4
    @11
    vc
    vex
    #
    vd
    vex
    #
    op1std
    #
    breq2d
    @50
    @42
    @34
    @43
    @35
    @50
    @15
    @3
    @0
    @53
    eqeq2d
    @50
    @19
    @4
    @1
    cS
    @3
    @4
    @11
    @51
    @52
    op2ndd
    breq2d
    anbi12d
    orbi12d
    anbi12d
    opelopab
    @32
    @39
    @37
    @26
    @27
    @29
    @30
    an4
    anbi1i
    3bitri
end
