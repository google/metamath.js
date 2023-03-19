include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "wa.mm"
include "wbr.mm"
include "co.mm"
include "cn.mm"
include "wral.mm"
include "copab.mm"
include "cinftm.mm"
include "cfv.mm"
include "wb.mm"
include "wceq.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "simpl.mm"
include "breq2d.mm"
include "oveq2d.mm"
include "simpr.mm"
include "breq12d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "eqid.mm"
include "brabga.mm"
include "3adant1.mm"
include "cvv.mm"
include "elex.mm"
include "3ad2ant1.mm"
include "cbs.mm"
include "c0g.mm"
include "cplt.mm"
include "cmg.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "eqidd.mm"
include "breq123d.mm"
include "oveqd.mm"
include "opabbidv.mm"
include "df-inftm.mm"
include "cxp.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "opabssxp.mm"
include "ssexi.mm"
include "fvmpt.mm"
include "syl.mm"
include "breqd.mm"
include "3simpc.mm"
include "biantrurd.mm"
include "3bitr4d.mm"

theorem isinftm
  let cB: class B
  let c.lt: class .<
  let c.x: class .x.
  let vn: setvar n
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  assume inftm.b: |- B = ( Base ` W )
  assume inftm.0: |- .0. = ( 0g ` W )
  assume inftm.x: |- .x. = ( .g ` W )
  assume inftm.l: |- .< = ( lt ` W )

  disjoint W n
  disjoint X n
  disjoint Y n
  disjoint w x
  disjoint w y
  disjoint B w
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint .< w
  disjoint .< x
  disjoint .< y
  disjoint .x. w
  disjoint .x. x
  disjoint .x. y
  disjoint .0. w
  disjoint .0. x
  disjoint .0. y
  assert |- ( ( W e. V /\ X e. B /\ Y e. B ) -> ( X ( <<< ` W ) Y <-> ( .0. .< X /\ A. n e. NN ( n .x. X ) .< Y ) ) )

  proof
    cW
    cV
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
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
    c.0
    @4
    c.lt
    wbr
    #
    vn
    cv
    #
    @4
    c.x
    co
    #
    @6
    c.lt
    wbr
    #
    vn
    cn
    wral
    #
    wa
    #
    wa
    #
    vx
    vy
    copab
    #
    wbr
    #
    @1
    @2
    wa
    #
    c.0
    cX
    c.lt
    wbr
    #
    @10
    cX
    c.x
    co
    #
    cY
    c.lt
    wbr
    #
    vn
    cn
    wral
    #
    wa
    #
    wa
    #
    cX
    cY
    cW
    cinftm
    cfv
    #
    wbr
    @23
    @1
    @2
    @17
    @24
    wb
    @0
    @15
    @24
    vx
    vy
    cX
    cY
    @16
    cB
    cB
    @4
    cX
    wceq
    #
    @6
    cY
    wceq
    #
    wa
    #
    @8
    @18
    @14
    @23
    @26
    @5
    @1
    @27
    @7
    @2
    @4
    cX
    cB
    eleq1
    @6
    cY
    cB
    eleq1
    bi2anan9
    @28
    @9
    @19
    @13
    @22
    @28
    @4
    cX
    c.0
    c.lt
    @26
    @27
    simpl
    #
    breq2d
    @28
    @12
    @21
    vn
    cn
    @28
    @11
    @20
    @6
    cY
    c.lt
    @28
    @4
    cX
    @10
    c.x
    @29
    oveq2d
    @26
    @27
    simpr
    breq12d
    ralbidv
    anbi12d
    anbi12d
    @16
    eqid
    brabga
    3adant1
    @3
    @25
    @16
    cX
    cY
    @3
    cW
    cvv
    wcel
    #
    @25
    @16
    wceq
    @0
    @1
    @30
    @2
    cW
    cV
    elex
    3ad2ant1
    vw
    cW
    @4
    vw
    cv
    #
    cbs
    cfv
    #
    wcel
    #
    @6
    @32
    wcel
    #
    wa
    #
    @31
    c0g
    cfv
    #
    @4
    @31
    cplt
    cfv
    #
    wbr
    #
    @10
    @4
    @31
    cmg
    cfv
    #
    co
    #
    @6
    @37
    wbr
    #
    vn
    cn
    wral
    #
    wa
    #
    wa
    #
    vx
    vy
    copab
    @16
    cvv
    cinftm
    @31
    cW
    wceq
    #
    @44
    @15
    vx
    vy
    @45
    @35
    @8
    @43
    @14
    @45
    @33
    @5
    @34
    @7
    @45
    @32
    cB
    @4
    @45
    @32
    cW
    cbs
    cfv
    #
    cB
    @31
    cW
    cbs
    fveq2
    inftm.b
    syl6eqr
    #
    eleq2d
    @45
    @32
    cB
    @6
    @47
    eleq2d
    anbi12d
    @45
    @38
    @9
    @42
    @13
    @45
    @36
    c.0
    @4
    @4
    @37
    c.lt
    @45
    @36
    cW
    c0g
    cfv
    c.0
    @31
    cW
    c0g
    fveq2
    inftm.0
    syl6eqr
    @45
    @37
    cW
    cplt
    cfv
    c.lt
    @31
    cW
    cplt
    fveq2
    inftm.l
    syl6eqr
    #
    @45
    @4
    eqidd
    breq123d
    @45
    @41
    @12
    vn
    cn
    @45
    @40
    @11
    @6
    @6
    @37
    c.lt
    @45
    @39
    c.x
    @10
    @4
    @45
    @39
    cW
    cmg
    cfv
    c.x
    @31
    cW
    cmg
    fveq2
    inftm.x
    syl6eqr
    oveqd
    @48
    @45
    @6
    eqidd
    breq123d
    ralbidv
    anbi12d
    anbi12d
    opabbidv
    vx
    vy
    vw
    vn
    df-inftm
    @16
    cB
    cB
    cxp
    cB
    cB
    cB
    @46
    cvv
    inftm.b
    cW
    cbs
    fvex
    eqeltri
    #
    @49
    xpex
    @14
    vx
    vy
    cB
    cB
    opabssxp
    ssexi
    fvmpt
    syl
    breqd
    @3
    @18
    @23
    @0
    @1
    @2
    3simpc
    biantrurd
    3bitr4d
end
