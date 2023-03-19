include "wcel.mm"
include "cmnd.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "c0.mm"
include "c0g.mm"
include "w3a.mm"
include "cmhm.mm"
include "c2o.mm"
include "cxp.mm"
include "cvv.mm"
include "con0.mm"
include "2on.mm"
include "xpexg.mm"
include "mpan2.mm"
include "frmdmnd.mm"
include "syl.mm"
include "cgrp.mm"
include "frgpgrp.mm"
include "grpmnd.mm"
include "jca.mm"
include "cec.mm"
include "cword.mm"
include "cid.mm"
include "frmdbas.mm"
include "wrdexg.mm"
include "fvi.mm"
include "eqtr4d.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "eqid.mm"
include "frgpeccl.mm"
include "fmptd.mm"
include "cconcat.mm"
include "wer.mm"
include "efger.mm"
include "wb.mm"
include "ereq2.mm"
include "mpbiri.mm"
include "adantr.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "divsfval.mm"
include "frmdadd.mm"
include "adantl.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "anbi12d.mm"
include "frgpadd.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "frgp0.mm"
include "simprd.mm"
include "3jca.mm"
include "frmd0.mm"
include "ismhm.mm"
include "sylanbrc.mm"

theorem frgpmhm
  let vx: setvar x
  let c.sm: class .~
  let cF: class F
  let cG: class G
  let cI: class I
  let cM: class M
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  assume frgpmhm.m: |- M = ( freeMnd ` ( I X. 2o ) )
  assume frgpmhm.w: |- W = ( Base ` M )
  assume frgpmhm.g: |- G = ( freeGrp ` I )
  assume frgpmhm.r: |- .~ = ( ~FG ` I )
  assume frgpmhm.f: |- F = ( x e. W |-> [ x ] .~ )

  disjoint G x
  disjoint I x
  disjoint V x
  disjoint W x
  disjoint .~ x
  disjoint a b
  disjoint F a
  disjoint F b
  disjoint a x
  disjoint G a
  disjoint b x
  disjoint G b
  disjoint I a
  disjoint I b
  disjoint V a
  disjoint V b
  disjoint W a
  disjoint W b
  disjoint M a
  disjoint M b
  assert |- ( I e. V -> F e. ( M MndHom G ) )

  proof
    cI
    cV
    wcel
    #
    cM
    cmnd
    wcel
    #
    cG
    cmnd
    wcel
    #
    wa
    cW
    cG
    cbs
    cfv
    #
    cF
    wf
    #
    va
    cv
    #
    vb
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    #
    cF
    cfv
    #
    @5
    cF
    cfv
    #
    @6
    cF
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vb
    cW
    wral
    va
    cW
    wral
    #
    c0
    cF
    cfv
    #
    cG
    c0g
    cfv
    #
    wceq
    #
    w3a
    cF
    cM
    cG
    cmhm
    co
    wcel
    @0
    @1
    @2
    @0
    cI
    c2o
    cxp
    #
    cvv
    wcel
    #
    @1
    @0
    c2o
    con0
    wcel
    @20
    2on
    cI
    c2o
    cV
    con0
    xpexg
    mpan2
    #
    @19
    cM
    cvv
    frgpmhm.m
    frmdmnd
    syl
    @0
    cG
    cgrp
    wcel
    #
    @2
    cG
    cI
    cV
    frgpmhm.g
    frgpgrp
    cG
    grpmnd
    syl
    jca
    @0
    @4
    @15
    @18
    @0
    vx
    cW
    vx
    cv
    #
    c.sm
    cec
    #
    @3
    cF
    @0
    @23
    cW
    wcel
    #
    wa
    @23
    @19
    cword
    #
    cid
    cfv
    #
    wcel
    #
    @24
    @3
    wcel
    @0
    @25
    @28
    @0
    cW
    @27
    @23
    @0
    @20
    cW
    @27
    wceq
    #
    @21
    @20
    cW
    @26
    @27
    cW
    @19
    cM
    cvv
    frgpmhm.m
    frgpmhm.w
    frmdbas
    @20
    @26
    cvv
    wcel
    @27
    @26
    wceq
    @19
    cvv
    wrdexg
    @26
    cvv
    fvi
    syl
    eqtr4d
    syl
    #
    eleq2d
    biimpa
    @3
    c.sm
    cG
    cI
    @27
    @23
    frgpmhm.g
    frgpmhm.r
    @27
    eqid
    #
    @3
    eqid
    #
    frgpeccl
    syl
    frgpmhm.f
    fmptd
    @0
    @14
    va
    vb
    cW
    cW
    @0
    @5
    cW
    wcel
    #
    @6
    cW
    wcel
    #
    wa
    #
    wa
    #
    @5
    @6
    cconcat
    co
    #
    cF
    cfv
    @37
    c.sm
    cec
    #
    @9
    @13
    @36
    vx
    @37
    c.sm
    cF
    cW
    @0
    cW
    c.sm
    wer
    #
    @35
    @0
    @39
    @27
    c.sm
    wer
    #
    c.sm
    cI
    @27
    @31
    frgpmhm.r
    efger
    @0
    @29
    @39
    @40
    wb
    @30
    cW
    @27
    c.sm
    ereq2
    syl
    mpbiri
    #
    adantr
    #
    cW
    cvv
    wcel
    #
    @36
    cW
    cM
    cbs
    cfv
    cvv
    frgpmhm.w
    cM
    cbs
    fvex
    eqeltri
    #
    a1i
    #
    frgpmhm.f
    divsfval
    @36
    @8
    @37
    cF
    @35
    @8
    @37
    wceq
    @0
    cW
    @7
    @19
    cM
    @5
    @6
    frgpmhm.m
    frgpmhm.w
    @7
    eqid
    #
    frmdadd
    adantl
    fveq2d
    @36
    @13
    @5
    c.sm
    cec
    #
    @6
    c.sm
    cec
    #
    @12
    co
    #
    @38
    @36
    @10
    @47
    @11
    @48
    @12
    @36
    vx
    @5
    c.sm
    cF
    cW
    @42
    @45
    frgpmhm.f
    divsfval
    @36
    vx
    @6
    c.sm
    cF
    cW
    @42
    @45
    frgpmhm.f
    divsfval
    oveq12d
    @36
    @5
    @27
    wcel
    #
    @6
    @27
    wcel
    #
    wa
    #
    @49
    @38
    wceq
    @0
    @35
    @52
    @0
    @33
    @50
    @34
    @51
    @0
    cW
    @27
    @5
    @30
    eleq2d
    @0
    cW
    @27
    @6
    @30
    eleq2d
    anbi12d
    biimpa
    @5
    @6
    @12
    c.sm
    cG
    cI
    @27
    @31
    frgpmhm.g
    frgpmhm.r
    @12
    eqid
    #
    frgpadd
    syl
    eqtrd
    3eqtr4d
    ralrimivva
    @0
    @16
    c0
    c.sm
    cec
    #
    @17
    @0
    vx
    c0
    c.sm
    cF
    cW
    @41
    @43
    @0
    @44
    a1i
    frgpmhm.f
    divsfval
    @0
    @22
    @54
    @17
    wceq
    c.sm
    cG
    cI
    cV
    frgpmhm.g
    frgpmhm.r
    frgp0
    simprd
    eqtrd
    3jca
    va
    vb
    cW
    @3
    @7
    @12
    cM
    cG
    cF
    @17
    c0
    frgpmhm.w
    @32
    @46
    @53
    @19
    cM
    frgpmhm.m
    frmd0
    @17
    eqid
    ismhm
    sylanbrc
end
