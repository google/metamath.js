include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cibl.mm"
include "i1ff.mm"
include "feqmptd.mm"
include "cmbf.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "citg2.mm"
include "cneg.mm"
include "i1fmbf.mm"
include "eqeltrrd.mm"
include "simpr.mm"
include "biantrurd.mm"
include "ifbid.mm"
include "mpteq2dva.mm"
include "fveq2d.mm"
include "c0p.mm"
include "cofr.mm"
include "wceq.mm"
include "eqid.mm"
include "i1fpos.mm"
include "csn.mm"
include "cxp.mm"
include "wral.mm"
include "0re.mm"
include "ffvelrnda.mm"
include "max1.mm"
include "sylancr.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "reex.mm"
include "a1i.mm"
include "fvex.mm"
include "c0ex.mm"
include "ifex.mm"
include "fconstmpt.mm"
include "eqidd.mm"
include "ofrfval2.mm"
include "mpbird.mm"
include "cc.mm"
include "wss.mm"
include "ax-resscn.mm"
include "wfn.mm"
include "fnmpti.mm"
include "0pledm.mm"
include "itg2itg1.mm"
include "syl2anc.mm"
include "eqtr3d.mm"
include "itg1cl.mm"
include "syl.mm"
include "eqeltrd.mm"
include "c1.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "neg1rr.mm"
include "offval2.mm"
include "recnd.mm"
include "mulm1d.mm"
include "eqtrd.mm"
include "id.mm"
include "i1fmulc.mm"
include "i1fposd.mm"
include "renegcld.mm"
include "negex.mm"
include "iblrelem.mm"
include "mpbir3and.mm"

theorem i1fibl
  let cF: class F
  let vx: setvar x


  assert |- ( F e. dom S.1 -> F e. L^1 )

  proof
    cF
    citg1
    cdm
    #
    wcel
    #
    cF
    vx
    cr
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    cibl
    @1
    vx
    cr
    cr
    cF
    cF
    i1ff
    #
    feqmptd
    #
    @1
    @4
    cibl
    wcel
    @4
    cmbf
    wcel
    vx
    cr
    @2
    cr
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    wa
    #
    @3
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    wcel
    vx
    cr
    @7
    cc0
    @3
    cneg
    #
    cle
    wbr
    #
    wa
    #
    @13
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    wcel
    @1
    cF
    @4
    cmbf
    @6
    cF
    i1fmbf
    eqeltrrd
    @1
    @12
    vx
    cr
    @8
    @3
    cc0
    cif
    #
    cmpt
    #
    citg1
    cfv
    #
    cr
    @1
    @20
    citg2
    cfv
    #
    @12
    @21
    @1
    @20
    @11
    citg2
    @1
    vx
    cr
    @19
    @10
    @1
    @7
    wa
    #
    @8
    @9
    @3
    cc0
    @23
    @7
    @8
    @1
    @7
    simpr
    #
    biantrurd
    ifbid
    mpteq2dva
    fveq2d
    @1
    @20
    @0
    wcel
    #
    c0p
    @20
    cle
    cofr
    #
    wbr
    #
    @22
    @21
    wceq
    vx
    cF
    @20
    @20
    eqid
    #
    i1fpos
    #
    @1
    @27
    cr
    cc0
    csn
    cxp
    #
    @20
    @26
    wbr
    #
    @1
    @31
    cc0
    @19
    cle
    wbr
    #
    vx
    cr
    wral
    @1
    @32
    vx
    cr
    @23
    cc0
    cr
    wcel
    #
    @3
    cr
    wcel
    @32
    0re
    @1
    cr
    cr
    @2
    cF
    @5
    ffvelrnda
    #
    cc0
    @3
    max1
    sylancr
    ralrimiva
    @1
    vx
    cr
    cc0
    @19
    cle
    @30
    @20
    cvv
    cr
    cvv
    cr
    cvv
    wcel
    @1
    reex
    a1i
    #
    @33
    @23
    0re
    a1i
    #
    @19
    cvv
    wcel
    @23
    @8
    @3
    cc0
    @2
    cF
    fvex
    c0ex
    ifex
    #
    a1i
    @30
    vx
    cr
    cc0
    cmpt
    wceq
    @1
    vx
    cr
    cc0
    fconstmpt
    a1i
    #
    @1
    @20
    eqidd
    ofrfval2
    mpbird
    @1
    cr
    @20
    cr
    cc
    wss
    @1
    ax-resscn
    a1i
    #
    @20
    cr
    wfn
    @1
    vx
    cr
    @19
    @20
    @37
    @28
    fnmpti
    a1i
    0pledm
    mpbird
    @20
    itg2itg1
    syl2anc
    eqtr3d
    @1
    @25
    @21
    cr
    wcel
    @29
    @20
    itg1cl
    syl
    eqeltrd
    @1
    @18
    vx
    cr
    @14
    @13
    cc0
    cif
    #
    cmpt
    #
    citg1
    cfv
    #
    cr
    @1
    @41
    citg2
    cfv
    #
    @18
    @42
    @1
    @41
    @17
    citg2
    @1
    vx
    cr
    @40
    @16
    @23
    @14
    @15
    @13
    cc0
    @23
    @7
    @14
    @24
    biantrurd
    ifbid
    mpteq2dva
    fveq2d
    @1
    @41
    @0
    wcel
    #
    c0p
    @41
    @26
    wbr
    #
    @43
    @42
    wceq
    @1
    vx
    @13
    @1
    cr
    c1
    cneg
    #
    csn
    cxp
    #
    cF
    cmul
    cof
    co
    #
    vx
    cr
    @13
    cmpt
    #
    @0
    @1
    @48
    vx
    cr
    @46
    @3
    cmul
    co
    #
    cmpt
    @49
    @1
    vx
    cr
    @46
    @3
    cmul
    @47
    cF
    cvv
    cr
    cr
    @35
    @46
    cr
    wcel
    #
    @23
    neg1rr
    a1i
    @34
    @47
    vx
    cr
    @46
    cmpt
    wceq
    @1
    vx
    cr
    @46
    fconstmpt
    a1i
    @6
    offval2
    @1
    vx
    cr
    @50
    @13
    @23
    @3
    @23
    @3
    @34
    recnd
    mulm1d
    mpteq2dva
    eqtrd
    @1
    @46
    cF
    @1
    id
    @51
    @1
    neg1rr
    a1i
    i1fmulc
    eqeltrrd
    i1fposd
    #
    @1
    @45
    @30
    @41
    @26
    wbr
    #
    @1
    @53
    cc0
    @40
    cle
    wbr
    #
    vx
    cr
    wral
    @1
    @54
    vx
    cr
    @23
    @33
    @13
    cr
    wcel
    @54
    0re
    @23
    @3
    @34
    renegcld
    cc0
    @13
    max1
    sylancr
    ralrimiva
    @1
    vx
    cr
    cc0
    @40
    cle
    @30
    @41
    cvv
    cr
    cvv
    @35
    @36
    @40
    cvv
    wcel
    @23
    @14
    @13
    cc0
    @3
    negex
    c0ex
    ifex
    #
    a1i
    @38
    @1
    @41
    eqidd
    ofrfval2
    mpbird
    @1
    cr
    @41
    @39
    @41
    cr
    wfn
    @1
    vx
    cr
    @40
    @41
    @55
    @41
    eqid
    fnmpti
    a1i
    0pledm
    mpbird
    @41
    itg2itg1
    syl2anc
    eqtr3d
    @1
    @44
    @42
    cr
    wcel
    @52
    @41
    itg1cl
    syl
    eqeltrd
    @1
    vx
    cr
    @3
    @34
    iblrelem
    mpbir3and
    eqeltrd
end
