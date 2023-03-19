include "cc0.mm"
include "cfv.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "c2.mm"
include "ctp.mm"
include "cv.mm"
include "cprod.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "cfn.mm"
include "wcel.mm"
include "tpfi.mm"
include "a1i.mm"
include "c3.mm"
include "cfzo.mm"
include "wf1o.mm"
include "wb.mm"
include "fzo0to3tp.mm"
include "f1oeq23.mm"
include "mp2an.mm"
include "sylib.mm"
include "wa.mm"
include "eqidd.mm"
include "cn.mm"
include "cr.mm"
include "wf.mm"
include "adantr.mm"
include "simpr.mm"
include "syl6eleqr.mm"
include "ffvelrnd.mm"
include "recnd.mm"
include "fprodf1o.mm"
include "ccom.mm"
include "cvv.mm"
include "cmpt.mm"
include "coeq1d.mm"
include "f1of.mm"
include "syl.mm"
include "ovexd.mm"
include "fex2.mm"
include "syl3anc.mm"
include "coexg.mm"
include "syl2anc.mm"
include "fvmptd.mm"
include "fveq1d.mm"
include "wfun.mm"
include "cdm.mm"
include "f1ofun.mm"
include "f1odm.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "fvco.mm"
include "eqtr2d.mm"
include "prodeq2dv.mm"
include "c0ex.mm"
include "1ex.mm"
include "tpid1.mm"
include "syl5eleqr.mm"
include "eqtrd.mm"
include "eleqtrri.mm"
include "eqeltrd.mm"
include "tpid2.mm"
include "wne.mm"
include "0ne1.mm"
include "2ex.mm"
include "tpid3.mm"
include "0ne2.mm"
include "1ne2.mm"
include "prodtp.mm"
include "3eqtr3d.mm"
include "mulassd.mm"

theorem hgt750lemg
  let wph: wff ph
  let cR: class R
  let cT: class T
  let cF: class F
  let cL: class L
  let cN: class N
  let vc: setvar c
  let vb: setvar b
  let va: setvar a
  assume hgt750lemg.f: |- F = ( c e. R |-> ( c o. T ) )
  assume hgt750lemg.t: |- ( ph -> T : ( 0 ..^ 3 ) -1-1-onto-> ( 0 ..^ 3 ) )
  assume hgt750lemg.n: |- ( ph -> N : ( 0 ..^ 3 ) --> NN )
  assume hgt750lemg.l: |- ( ph -> L : NN --> RR )
  assume hgt750lemg.1: |- ( ph -> N e. R )

  disjoint N c
  disjoint R c
  disjoint T c
  disjoint c ph
  disjoint F b
  disjoint L a
  disjoint L b
  disjoint a b
  disjoint N a
  disjoint N b
  disjoint a c
  disjoint b c
  disjoint T a
  disjoint T b
  disjoint a ph
  disjoint b ph
  assert |- ( ph -> ( ( L ` ( ( F ` N ) ` 0 ) ) x. ( ( L ` ( ( F ` N ) ` 1 ) ) x. ( L ` ( ( F ` N ) ` 2 ) ) ) ) = ( ( L ` ( N ` 0 ) ) x. ( ( L ` ( N ` 1 ) ) x. ( L ` ( N ` 2 ) ) ) ) )

  proof
    wph
    cc0
    cN
    cF
    cfv
    #
    cfv
    #
    cL
    cfv
    #
    c1
    @0
    cfv
    #
    cL
    cfv
    #
    cmul
    co
    c2
    @0
    cfv
    #
    cL
    cfv
    #
    cmul
    co
    #
    cc0
    cN
    cfv
    #
    cL
    cfv
    #
    c1
    cN
    cfv
    #
    cL
    cfv
    #
    cmul
    co
    c2
    cN
    cfv
    #
    cL
    cfv
    #
    cmul
    co
    #
    @2
    @4
    @6
    cmul
    co
    cmul
    co
    @9
    @11
    @13
    cmul
    co
    cmul
    co
    wph
    cc0
    c1
    c2
    ctp
    #
    vb
    cv
    #
    @0
    cfv
    #
    cL
    cfv
    #
    vb
    cprod
    #
    @15
    va
    cv
    #
    cN
    cfv
    #
    cL
    cfv
    #
    va
    cprod
    #
    @7
    @14
    wph
    @23
    @15
    @16
    cT
    cfv
    #
    cN
    cfv
    #
    cL
    cfv
    #
    vb
    cprod
    @19
    wph
    @15
    @22
    @15
    @26
    va
    vb
    cT
    @24
    @20
    @24
    wceq
    @21
    @25
    cL
    @20
    @24
    cN
    fveq2
    fveq2d
    @15
    cfn
    wcel
    wph
    cc0
    c1
    c2
    tpfi
    a1i
    wph
    cc0
    c3
    cfzo
    co
    #
    @27
    cT
    wf1o
    #
    @15
    @15
    cT
    wf1o
    #
    hgt750lemg.t
    @27
    @15
    wceq
    #
    @30
    @28
    @29
    wb
    fzo0to3tp
    fzo0to3tp
    @27
    @15
    @27
    @15
    cT
    f1oeq23
    mp2an
    sylib
    #
    wph
    @16
    @15
    wcel
    #
    wa
    #
    @24
    eqidd
    wph
    @20
    @15
    wcel
    #
    wa
    #
    @22
    @35
    cn
    cr
    @21
    cL
    wph
    cn
    cr
    cL
    wf
    @34
    hgt750lemg.l
    adantr
    @35
    @27
    cn
    @20
    cN
    wph
    @27
    cn
    cN
    wf
    @34
    hgt750lemg.n
    adantr
    @35
    @20
    @15
    @27
    wph
    @34
    simpr
    fzo0to3tp
    syl6eleqr
    ffvelrnd
    ffvelrnd
    recnd
    fprodf1o
    wph
    @15
    @26
    @18
    vb
    @33
    @25
    @17
    cL
    @33
    @17
    @16
    cN
    cT
    ccom
    #
    cfv
    #
    @25
    @33
    @16
    @0
    @36
    wph
    @0
    @36
    wceq
    @32
    wph
    vc
    cN
    vc
    cv
    #
    cT
    ccom
    #
    @36
    cR
    cF
    cvv
    cF
    vc
    cR
    @39
    cmpt
    wceq
    wph
    hgt750lemg.f
    a1i
    wph
    @38
    cN
    wceq
    #
    wa
    @38
    cN
    cT
    wph
    @40
    simpr
    coeq1d
    hgt750lemg.1
    wph
    cN
    cR
    wcel
    cT
    cvv
    wcel
    #
    @36
    cvv
    wcel
    hgt750lemg.1
    wph
    @27
    @27
    cT
    wf
    #
    @27
    cvv
    wcel
    #
    @43
    @41
    wph
    @28
    @42
    hgt750lemg.t
    @27
    @27
    cT
    f1of
    syl
    #
    wph
    cc0
    c3
    cfzo
    ovexd
    #
    @45
    @27
    @27
    cT
    cvv
    cvv
    fex2
    syl3anc
    cN
    cT
    cR
    cvv
    coexg
    syl2anc
    fvmptd
    #
    adantr
    fveq1d
    @33
    cT
    wfun
    #
    @16
    cT
    cdm
    #
    wcel
    #
    @37
    @25
    wceq
    wph
    @47
    @32
    wph
    @28
    @47
    hgt750lemg.t
    @27
    @27
    cT
    f1ofun
    syl
    #
    adantr
    wph
    @49
    @32
    wph
    @48
    @15
    @16
    wph
    @29
    @48
    @15
    wceq
    @31
    @15
    @15
    cT
    f1odm
    syl
    #
    eleq2d
    biimpar
    @16
    cN
    cT
    fvco
    syl2anc
    eqtr2d
    fveq2d
    prodeq2dv
    eqtr2d
    wph
    cc0
    c1
    c2
    @18
    vb
    @2
    @4
    @6
    cvv
    cvv
    cvv
    @16
    cc0
    wceq
    @17
    @1
    cL
    @16
    cc0
    @0
    fveq2
    fveq2d
    @16
    c1
    wceq
    @17
    @3
    cL
    @16
    c1
    @0
    fveq2
    fveq2d
    cc0
    cvv
    wcel
    wph
    c0ex
    a1i
    #
    c1
    cvv
    wcel
    wph
    1ex
    a1i
    #
    wph
    @2
    wph
    cn
    cr
    @1
    cL
    hgt750lemg.l
    wph
    @1
    cc0
    cT
    cfv
    #
    cN
    cfv
    #
    cn
    wph
    @1
    cc0
    @36
    cfv
    #
    @55
    wph
    cc0
    @0
    @36
    @46
    fveq1d
    wph
    @47
    cc0
    @48
    wcel
    @56
    @55
    wceq
    @50
    wph
    cc0
    @15
    @48
    cc0
    c1
    c2
    c0ex
    tpid1
    #
    @51
    syl5eleqr
    cc0
    cN
    cT
    fvco
    syl2anc
    eqtrd
    wph
    @27
    cn
    @54
    cN
    hgt750lemg.n
    wph
    @27
    @27
    cc0
    cT
    @44
    cc0
    @27
    wcel
    wph
    cc0
    @15
    @27
    @57
    fzo0to3tp
    eleqtrri
    a1i
    #
    ffvelrnd
    ffvelrnd
    eqeltrd
    ffvelrnd
    recnd
    #
    wph
    @4
    wph
    cn
    cr
    @3
    cL
    hgt750lemg.l
    wph
    @3
    c1
    cT
    cfv
    #
    cN
    cfv
    #
    cn
    wph
    @3
    c1
    @36
    cfv
    #
    @61
    wph
    c1
    @0
    @36
    @46
    fveq1d
    wph
    @47
    c1
    @48
    wcel
    @62
    @61
    wceq
    @50
    wph
    c1
    @15
    @48
    cc0
    c1
    c2
    1ex
    tpid2
    #
    @51
    syl5eleqr
    c1
    cN
    cT
    fvco
    syl2anc
    eqtrd
    wph
    @27
    cn
    @60
    cN
    hgt750lemg.n
    wph
    @27
    @27
    c1
    cT
    @44
    c1
    @27
    wcel
    wph
    c1
    @15
    @27
    @63
    fzo0to3tp
    eleqtrri
    a1i
    #
    ffvelrnd
    ffvelrnd
    eqeltrd
    ffvelrnd
    recnd
    #
    cc0
    c1
    wne
    wph
    0ne1
    a1i
    #
    @16
    c2
    wceq
    @17
    @5
    cL
    @16
    c2
    @0
    fveq2
    fveq2d
    c2
    cvv
    wcel
    wph
    2ex
    a1i
    #
    wph
    @6
    wph
    cn
    cr
    @5
    cL
    hgt750lemg.l
    wph
    @5
    c2
    cT
    cfv
    #
    cN
    cfv
    #
    cn
    wph
    @5
    c2
    @36
    cfv
    #
    @69
    wph
    c2
    @0
    @36
    @46
    fveq1d
    wph
    @47
    c2
    @48
    wcel
    @70
    @69
    wceq
    @50
    wph
    c2
    @15
    @48
    cc0
    c1
    c2
    2ex
    tpid3
    #
    @51
    syl5eleqr
    c2
    cN
    cT
    fvco
    syl2anc
    eqtrd
    wph
    @27
    cn
    @68
    cN
    hgt750lemg.n
    wph
    @27
    @27
    c2
    cT
    @44
    c2
    @27
    wcel
    wph
    c2
    @15
    @27
    @71
    fzo0to3tp
    eleqtrri
    a1i
    #
    ffvelrnd
    ffvelrnd
    eqeltrd
    ffvelrnd
    recnd
    #
    cc0
    c2
    wne
    wph
    0ne2
    a1i
    #
    c1
    c2
    wne
    wph
    1ne2
    a1i
    #
    prodtp
    wph
    cc0
    c1
    c2
    @22
    va
    @9
    @11
    @13
    cvv
    cvv
    cvv
    @20
    cc0
    wceq
    @21
    @8
    cL
    @20
    cc0
    cN
    fveq2
    fveq2d
    @20
    c1
    wceq
    @21
    @10
    cL
    @20
    c1
    cN
    fveq2
    fveq2d
    @52
    @53
    wph
    @9
    wph
    cn
    cr
    @8
    cL
    hgt750lemg.l
    wph
    @27
    cn
    cc0
    cN
    hgt750lemg.n
    @58
    ffvelrnd
    ffvelrnd
    recnd
    #
    wph
    @11
    wph
    cn
    cr
    @10
    cL
    hgt750lemg.l
    wph
    @27
    cn
    c1
    cN
    hgt750lemg.n
    @64
    ffvelrnd
    ffvelrnd
    recnd
    #
    @66
    @20
    c2
    wceq
    @21
    @12
    cL
    @20
    c2
    cN
    fveq2
    fveq2d
    @67
    wph
    @13
    wph
    cn
    cr
    @12
    cL
    hgt750lemg.l
    wph
    @27
    cn
    c2
    cN
    hgt750lemg.n
    @72
    ffvelrnd
    ffvelrnd
    recnd
    #
    @74
    @75
    prodtp
    3eqtr3d
    wph
    @2
    @4
    @6
    @59
    @65
    @73
    mulassd
    wph
    @9
    @11
    @13
    @76
    @77
    @78
    mulassd
    3eqtr3d
end
