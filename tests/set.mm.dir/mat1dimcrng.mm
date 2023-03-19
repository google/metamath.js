include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "crg.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "csn.mm"
include "cfn.mm"
include "snfi.mm"
include "crngring.mm"
include "adantr.mm"
include "matring.mm"
include "sylancr.mm"
include "cop.mm"
include "wrex.mm"
include "wb.mm"
include "mat1dimelbas.mm"
include "anbi12d.mm"
include "sylan.mm"
include "wi.mm"
include "simpll.mm"
include "simprl.mm"
include "simprr.mm"
include "eqid.mm"
include "crngcom.mm"
include "syl3anc.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "anim1i.mm"
include "mat1dimmul.mm"
include "pm3.22.mm"
include "syl2an.mm"
include "3eqtr4d.mm"
include "expr.mm"
include "imp.mm"
include "oveq12.mm"
include "ex.mm"
include "ad2antlr.mm"
include "expcom.mm"
include "rexlimdva.mm"
include "impd.mm"
include "sylbid.mm"
include "ralrimivv.mm"
include "iscrng2.mm"
include "sylanbrc.mm"

theorem mat1dimcrng
  let cA: class A
  let cB: class B
  let cR: class R
  let cE: class E
  let cO: class O
  let cV: class V
  let vr: setvar r
  let cM: class M
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cY: class Y
  let vk: setvar k
  let va: setvar a
  let vb: setvar b
  assume mat1dim.a: |- A = ( { E } Mat R )
  assume mat1dim.b: |- B = ( Base ` R )
  assume mat1dim.o: |- O = <. E , E >.


  assert |- ( ( R e. CRing /\ E e. V ) -> A e. CRing )

  proof
    cR
    ccrg
    wcel
    #
    cE
    cV
    wcel
    #
    wa
    #
    cA
    crg
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cA
    cmulr
    cfv
    #
    co
    #
    @5
    @4
    @6
    co
    #
    wceq
    #
    vy
    cA
    cbs
    cfv
    #
    wral
    vx
    @10
    wral
    cA
    ccrg
    wcel
    @2
    cE
    csn
    #
    cfn
    wcel
    cR
    crg
    wcel
    #
    @3
    cE
    snfi
    @0
    @12
    @1
    cR
    crngring
    #
    adantr
    cA
    cR
    @11
    mat1dim.a
    matring
    sylancr
    @2
    @9
    vx
    vy
    @10
    @10
    @2
    @4
    @10
    wcel
    #
    @5
    @10
    wcel
    #
    wa
    #
    @4
    cO
    va
    cv
    #
    cop
    csn
    #
    wceq
    #
    va
    cB
    wrex
    #
    @5
    cO
    vb
    cv
    #
    cop
    csn
    #
    wceq
    #
    vb
    cB
    wrex
    #
    wa
    #
    @9
    @0
    @12
    @1
    @16
    @25
    wb
    @13
    @12
    @1
    wa
    #
    @14
    @20
    @15
    @24
    cA
    cB
    cR
    cE
    @4
    cO
    cV
    va
    mat1dim.a
    mat1dim.b
    mat1dim.o
    mat1dimelbas
    cA
    cB
    cR
    cE
    @5
    cO
    cV
    vb
    mat1dim.a
    mat1dim.b
    mat1dim.o
    mat1dimelbas
    anbi12d
    sylan
    @2
    @20
    @24
    @9
    @2
    @19
    @24
    @9
    wi
    #
    va
    cB
    @2
    @17
    cB
    wcel
    #
    wa
    #
    @19
    @27
    @29
    @19
    wa
    #
    @23
    @9
    vb
    cB
    @30
    @21
    cB
    wcel
    #
    wa
    #
    @23
    @9
    @32
    @23
    wa
    @18
    @22
    @6
    co
    #
    @22
    @18
    @6
    co
    #
    @7
    @8
    @32
    @33
    @34
    wceq
    #
    @23
    @30
    @31
    @35
    @29
    @31
    @35
    wi
    @19
    @2
    @28
    @31
    @35
    @2
    @28
    @31
    wa
    #
    wa
    #
    cO
    @17
    @21
    cR
    cmulr
    cfv
    #
    co
    #
    cop
    #
    csn
    #
    cO
    @21
    @17
    @38
    co
    #
    cop
    #
    csn
    #
    @33
    @34
    @37
    @40
    @43
    @37
    @39
    @42
    cO
    @37
    @0
    @28
    @31
    @39
    @42
    wceq
    @0
    @1
    @36
    simpll
    @2
    @28
    @31
    simprl
    @2
    @28
    @31
    simprr
    cB
    cR
    @38
    @17
    @21
    mat1dim.b
    @38
    eqid
    crngcom
    syl3anc
    opeq2d
    sneqd
    @2
    @26
    @36
    @33
    @41
    wceq
    @0
    @12
    @1
    @13
    anim1i
    #
    cA
    cB
    cR
    cE
    cO
    cV
    @17
    @21
    mat1dim.a
    mat1dim.b
    mat1dim.o
    mat1dimmul
    sylan
    @2
    @26
    @31
    @28
    wa
    @34
    @44
    wceq
    @36
    @45
    @28
    @31
    pm3.22
    cA
    cB
    cR
    cE
    cO
    cV
    @21
    @17
    mat1dim.a
    mat1dim.b
    mat1dim.o
    mat1dimmul
    syl2an
    3eqtr4d
    expr
    adantr
    imp
    adantr
    @32
    @23
    @7
    @33
    wceq
    #
    @19
    @23
    @46
    wi
    @29
    @31
    @19
    @23
    @46
    @4
    @18
    @5
    @22
    @6
    oveq12
    ex
    ad2antlr
    imp
    @32
    @23
    @8
    @34
    wceq
    #
    @19
    @23
    @47
    wi
    @29
    @31
    @23
    @19
    @47
    @5
    @22
    @4
    @18
    @6
    oveq12
    expcom
    ad2antlr
    imp
    3eqtr4d
    ex
    rexlimdva
    ex
    rexlimdva
    impd
    sylbid
    ralrimivv
    vx
    vy
    @10
    cA
    @6
    @10
    eqid
    @6
    eqid
    iscrng2
    sylanbrc
end
