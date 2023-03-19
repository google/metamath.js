include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "cv.mm"
include "cfv.mm"
include "citg.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cneg.mm"
include "cmin.mm"
include "co.mm"
include "cmpt.mm"
include "cof.mm"
include "i1ff.mm"
include "ffvelrnda.mm"
include "cibl.mm"
include "feqmptd.mm"
include "i1fibl.mm"
include "eqeltrrd.mm"
include "itgreval.mm"
include "citg2.mm"
include "wa.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "max1.mm"
include "sylancr.mm"
include "id.mm"
include "i1fposd.mm"
include "syl.mm"
include "itgitg2.mm"
include "c0p.mm"
include "cofr.mm"
include "wceq.mm"
include "csn.mm"
include "cxp.mm"
include "wral.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "reex.mm"
include "a1i.mm"
include "fconstmpt.mm"
include "eqidd.mm"
include "ofrfval2.mm"
include "mpbird.mm"
include "cc.mm"
include "wss.mm"
include "ax-resscn.mm"
include "wf.mm"
include "wfn.mm"
include "eqid.mm"
include "fmptd.mm"
include "ffn.mm"
include "0pledm.mm"
include "itg2itg1.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "renegcld.mm"
include "c1.mm"
include "cmul.mm"
include "neg1rr.mm"
include "offval2.mm"
include "recnd.mm"
include "mulm1d.mm"
include "mpteq2dva.mm"
include "i1fmulc.mm"
include "oveq12d.mm"
include "itg1sub.mm"
include "eqtr4d.mm"
include "max0sub.mm"
include "3eqtr4d.mm"
include "fveq2d.mm"
include "3eqtrd.mm"

theorem itgitg1
  let vx: setvar x
  let cF: class F

  disjoint F x
  assert |- ( F e. dom S.1 -> S. RR ( F ` x ) _d x = ( S.1 ` F ) )

  proof
    cF
    citg1
    cdm
    #
    wcel
    #
    vx
    cr
    vx
    cv
    #
    cF
    cfv
    #
    citg
    vx
    cr
    cc0
    @3
    cle
    wbr
    #
    @3
    cc0
    cif
    #
    citg
    #
    vx
    cr
    cc0
    @3
    cneg
    #
    cle
    wbr
    #
    @7
    cc0
    cif
    #
    citg
    #
    cmin
    co
    #
    vx
    cr
    @5
    cmpt
    #
    vx
    cr
    @9
    cmpt
    #
    cmin
    cof
    co
    #
    citg1
    cfv
    #
    cF
    citg1
    cfv
    @1
    vx
    cr
    @3
    @1
    cr
    cr
    @2
    cF
    cF
    i1ff
    #
    ffvelrnda
    #
    @1
    cF
    vx
    cr
    @3
    cmpt
    #
    cibl
    @1
    vx
    cr
    cr
    cF
    @16
    feqmptd
    #
    cF
    i1fibl
    eqeltrrd
    itgreval
    @1
    @11
    @12
    citg1
    cfv
    #
    @13
    citg1
    cfv
    #
    cmin
    co
    #
    @15
    @1
    @6
    @20
    @10
    @21
    cmin
    @1
    @6
    @12
    citg2
    cfv
    #
    @20
    @1
    vx
    @5
    @1
    @2
    cr
    wcel
    wa
    #
    @3
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @5
    cr
    wcel
    @17
    0re
    @4
    @3
    cc0
    cr
    ifcl
    sylancl
    #
    @24
    @26
    @25
    cc0
    @5
    cle
    wbr
    #
    0re
    @17
    cc0
    @3
    max1
    sylancr
    #
    @1
    @12
    @0
    wcel
    #
    @12
    cibl
    wcel
    @1
    vx
    @3
    @1
    cF
    @18
    @0
    @19
    @1
    id
    #
    eqeltrrd
    i1fposd
    #
    @12
    i1fibl
    syl
    itgitg2
    @1
    @30
    c0p
    @12
    cle
    cofr
    #
    wbr
    #
    @23
    @20
    wceq
    @32
    @1
    @34
    cr
    cc0
    csn
    cxp
    #
    @12
    @33
    wbr
    #
    @1
    @36
    @28
    vx
    cr
    wral
    @1
    @28
    vx
    cr
    @29
    ralrimiva
    @1
    vx
    cr
    cc0
    @5
    cle
    @35
    @12
    cvv
    cr
    cr
    cr
    cvv
    wcel
    @1
    reex
    a1i
    #
    @26
    @24
    0re
    a1i
    #
    @27
    @35
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
    @12
    eqidd
    #
    ofrfval2
    mpbird
    @1
    cr
    @12
    cr
    cc
    wss
    @1
    ax-resscn
    a1i
    #
    @1
    cr
    cr
    @12
    wf
    @12
    cr
    wfn
    @1
    vx
    cr
    @5
    cr
    @12
    @27
    @12
    eqid
    fmptd
    cr
    cr
    @12
    ffn
    syl
    0pledm
    mpbird
    @12
    itg2itg1
    syl2anc
    eqtrd
    @1
    @10
    @13
    citg2
    cfv
    #
    @21
    @1
    vx
    @9
    @24
    @7
    cr
    wcel
    #
    @26
    @9
    cr
    wcel
    @24
    @3
    @17
    renegcld
    #
    0re
    @8
    @7
    cc0
    cr
    ifcl
    sylancl
    #
    @24
    @26
    @43
    cc0
    @9
    cle
    wbr
    #
    0re
    @44
    cc0
    @7
    max1
    sylancr
    #
    @1
    @13
    @0
    wcel
    #
    @13
    cibl
    wcel
    @1
    vx
    @7
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
    @7
    cmpt
    #
    @0
    @1
    @51
    vx
    cr
    @49
    @3
    cmul
    co
    #
    cmpt
    @52
    @1
    vx
    cr
    @49
    @3
    cmul
    @50
    cF
    cvv
    cr
    cr
    @37
    @49
    cr
    wcel
    #
    @24
    neg1rr
    a1i
    @17
    @50
    vx
    cr
    @49
    cmpt
    wceq
    @1
    vx
    cr
    @49
    fconstmpt
    a1i
    @19
    offval2
    @1
    vx
    cr
    @53
    @7
    @24
    @3
    @24
    @3
    @17
    recnd
    mulm1d
    mpteq2dva
    eqtrd
    @1
    @49
    cF
    @31
    @54
    @1
    neg1rr
    a1i
    i1fmulc
    eqeltrrd
    i1fposd
    #
    @13
    i1fibl
    syl
    itgitg2
    @1
    @48
    c0p
    @13
    @33
    wbr
    #
    @42
    @21
    wceq
    @55
    @1
    @56
    @35
    @13
    @33
    wbr
    #
    @1
    @57
    @46
    vx
    cr
    wral
    @1
    @46
    vx
    cr
    @47
    ralrimiva
    @1
    vx
    cr
    cc0
    @9
    cle
    @35
    @13
    cvv
    cr
    cr
    @37
    @38
    @45
    @39
    @1
    @13
    eqidd
    #
    ofrfval2
    mpbird
    @1
    cr
    @13
    @41
    @1
    cr
    cr
    @13
    wf
    @13
    cr
    wfn
    @1
    vx
    cr
    @9
    cr
    @13
    @45
    @13
    eqid
    fmptd
    cr
    cr
    @13
    ffn
    syl
    0pledm
    mpbird
    @13
    itg2itg1
    syl2anc
    eqtrd
    oveq12d
    @1
    @30
    @48
    @15
    @22
    wceq
    @32
    @55
    @12
    @13
    itg1sub
    syl2anc
    eqtr4d
    @1
    @14
    cF
    citg1
    @1
    vx
    cr
    @5
    @9
    cmin
    co
    #
    cmpt
    @18
    @14
    cF
    @1
    vx
    cr
    @59
    @3
    @24
    @25
    @59
    @3
    wceq
    @17
    @3
    max0sub
    syl
    mpteq2dva
    @1
    vx
    cr
    @5
    @9
    cmin
    @12
    @13
    cvv
    cr
    cr
    @37
    @27
    @45
    @40
    @58
    offval2
    @19
    3eqtr4d
    fveq2d
    3eqtrd
end
