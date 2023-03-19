include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "cgsu.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cres.mm"
include "cixp.mm"
include "crab.mm"
include "wrex.mm"
include "cdprd.mm"
include "cdm.mm"
include "csubg.mm"
include "wf.mm"
include "wb.mm"
include "dprdf2.mm"
include "fssresd.mm"
include "fdm.mm"
include "eqid.mm"
include "eldprd.mm"
include "3syl.mm"
include "mpbid.mm"
include "simprd.mm"
include "adantr.mm"
include "cif.mm"
include "cmpt.mm"
include "simprr.mm"
include "cbs.mm"
include "simpld.mm"
include "ad2antrr.mm"
include "syl.mm"
include "simprl.mm"
include "dprdff.mm"
include "feqmptd.mm"
include "wss.mm"
include "resmptd.mm"
include "iftrue.mm"
include "mpteq2ia.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "cvv.mm"
include "ccntz.mm"
include "cgrp.mm"
include "cmnd.mm"
include "dprdgrp.mm"
include "grpmnd.mm"
include "dprddomcld.mm"
include "simplrl.mm"
include "dprdfcl.mm"
include "fvres.mm"
include "adantl.mm"
include "eleqtrd.mm"
include "wn.mm"
include "ffvelrnda.mm"
include "subg0cl.mm"
include "ifclda.mm"
include "wfun.mm"
include "csupp.mm"
include "mptexg.mm"
include "funmpt.mm"
include "a1i.mm"
include "dprdffsupp.mm"
include "simpr.mm"
include "eldifn.mm"
include "ad2antlr.mm"
include "eldifd.mm"
include "ssid.mm"
include "ssexd.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "suppssr.mm"
include "adantlr.mm"
include "syldan.mm"
include "ifeq1da.mm"
include "ifid.mm"
include "suppss2.mm"
include "fsuppsssupp.mm"
include "syl22anc.mm"
include "dprdwd.mm"
include "dprdfcntz.mm"
include "iffalsed.mm"
include "gsumzres.mm"
include "3eqtrd.mm"
include "dprdf11.mm"
include "fveq1d.mm"
include "eldifi.mm"
include "eleq1.mm"
include "fveq2.mm"
include "ifbieq1d.mm"
include "ifex.mm"
include "fvmpt3i.mm"
include "rexlimddv.mm"

theorem dmdprdsplitlem
  let wph: wff ph
  let cA: class A
  let cS: class S
  let vh: setvar h
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cI: class I
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vf: setvar f
  let vn: setvar n
  assume dmdprdsplitlem.0: |- .0. = ( 0g ` G )
  assume dmdprdsplitlem.w: |- W = { h e. X_ i e. I ( S ` i ) | h finSupp .0. }
  assume dmdprdsplitlem.1: |- ( ph -> G dom DProd S )
  assume dmdprdsplitlem.2: |- ( ph -> dom S = I )
  assume dmdprdsplitlem.3: |- ( ph -> A C_ I )
  assume dmdprdsplitlem.4: |- ( ph -> F e. W )
  assume dmdprdsplitlem.5: |- ( ph -> ( G gsum F ) e. ( G DProd ( S |` A ) ) )

  disjoint .0. h
  disjoint h i
  disjoint A h
  disjoint A i
  disjoint G h
  disjoint G i
  disjoint I h
  disjoint I i
  disjoint F h
  disjoint S h
  disjoint S i
  disjoint f h
  disjoint f n
  disjoint .0. f
  disjoint h n
  disjoint .0. n
  disjoint f i
  disjoint A f
  disjoint i n
  disjoint A n
  disjoint G f
  disjoint G n
  disjoint I f
  disjoint I n
  disjoint F f
  disjoint F n
  disjoint f ph
  disjoint n ph
  disjoint S f
  disjoint S n
  disjoint X f
  disjoint X n
  assert |- ( ( ph /\ X e. ( I \ A ) ) -> ( F ` X ) = .0. )

  proof
    wph
    cX
    cI
    cA
    cdif
    #
    wcel
    #
    wa
    #
    cG
    cF
    cgsu
    co
    #
    cG
    vf
    cv
    #
    cgsu
    co
    #
    wceq
    #
    cX
    cF
    cfv
    #
    c.0
    wceq
    vf
    vh
    cv
    c.0
    cfsupp
    wbr
    vh
    vi
    cA
    vi
    cv
    cS
    cA
    cres
    #
    cfv
    cixp
    crab
    #
    wph
    @6
    vf
    @9
    wrex
    #
    @1
    wph
    cG
    @8
    cdprd
    cdm
    #
    wbr
    #
    @10
    wph
    @3
    cG
    @8
    cdprd
    co
    wcel
    #
    @12
    @10
    wa
    #
    dmdprdsplitlem.5
    wph
    cA
    cG
    csubg
    cfv
    #
    @8
    wf
    #
    @8
    cdm
    cA
    wceq
    #
    @13
    @14
    wb
    wph
    cI
    @15
    cA
    cS
    wph
    cS
    cG
    cI
    dmdprdsplitlem.1
    dmdprdsplitlem.2
    dprdf2
    #
    dmdprdsplitlem.3
    fssresd
    #
    cA
    @15
    @8
    fdm
    #
    @3
    @8
    vf
    vh
    vi
    cG
    cA
    @9
    c.0
    dmdprdsplitlem.0
    @9
    eqid
    #
    eldprd
    3syl
    mpbid
    #
    simprd
    adantr
    @2
    @4
    @9
    wcel
    #
    @6
    wa
    #
    wa
    #
    @7
    cX
    vn
    cI
    vn
    cv
    #
    cA
    wcel
    #
    @26
    @4
    cfv
    #
    c.0
    cif
    #
    cmpt
    #
    cfv
    #
    cX
    cA
    wcel
    #
    cX
    @4
    cfv
    #
    c.0
    cif
    #
    c.0
    @25
    cX
    cF
    @30
    @25
    @3
    cG
    @30
    cgsu
    co
    #
    wceq
    cF
    @30
    wceq
    @25
    @3
    @5
    cG
    @30
    cA
    cres
    #
    cgsu
    co
    @35
    @2
    @23
    @6
    simprr
    @25
    @4
    @36
    cG
    cgsu
    @25
    @4
    vn
    cA
    @28
    cmpt
    #
    @36
    @25
    vn
    cA
    cG
    cbs
    cfv
    #
    @4
    @25
    @38
    @8
    vh
    vi
    @4
    cG
    cA
    @9
    c.0
    @21
    wph
    @12
    @1
    @24
    wph
    @12
    @10
    @22
    simpld
    ad2antrr
    #
    wph
    @17
    @1
    @24
    wph
    @16
    @17
    @19
    @20
    syl
    ad2antrr
    #
    @2
    @23
    @6
    simprl
    #
    @38
    eqid
    #
    dprdff
    #
    feqmptd
    @25
    @36
    vn
    cA
    @29
    cmpt
    @37
    @25
    vn
    cI
    cA
    @29
    wph
    cA
    cI
    wss
    @1
    @24
    dmdprdsplitlem.3
    ad2antrr
    resmptd
    vn
    cA
    @29
    @28
    @27
    @28
    c.0
    iftrue
    mpteq2ia
    syl6eq
    eqtr4d
    oveq2d
    @25
    cI
    @38
    @30
    cG
    cvv
    cA
    c.0
    cG
    ccntz
    cfv
    #
    @42
    dmdprdsplitlem.0
    @44
    eqid
    #
    @25
    cG
    cS
    @11
    wbr
    #
    cG
    cgrp
    wcel
    cG
    cmnd
    wcel
    wph
    @46
    @1
    @24
    dmdprdsplitlem.1
    ad2antrr
    #
    cS
    cG
    dprdgrp
    cG
    grpmnd
    3syl
    wph
    cI
    cvv
    wcel
    #
    @1
    @24
    wph
    cS
    cG
    cI
    dmdprdsplitlem.1
    dmdprdsplitlem.2
    dprddomcld
    #
    ad2antrr
    #
    @25
    @38
    cS
    vh
    vi
    @30
    cG
    cI
    cW
    c.0
    dmdprdsplitlem.w
    @47
    wph
    cS
    cdm
    cI
    wceq
    @1
    @24
    dmdprdsplitlem.2
    ad2antrr
    #
    @25
    vn
    @29
    cS
    vh
    vi
    cG
    cI
    cW
    c.0
    dmdprdsplitlem.w
    @47
    @51
    @25
    @26
    cI
    wcel
    #
    wa
    #
    @27
    @28
    c.0
    @26
    cS
    cfv
    #
    @53
    @27
    wa
    @28
    @26
    @8
    cfv
    #
    @54
    @53
    @8
    vh
    vi
    @4
    cG
    cA
    @9
    @26
    c.0
    @21
    @25
    @12
    @52
    @39
    adantr
    @25
    @17
    @52
    @40
    adantr
    @2
    @23
    @6
    @52
    simplrl
    dprdfcl
    @27
    @55
    @54
    wceq
    @53
    @26
    cA
    cS
    fvres
    adantl
    eleqtrd
    @53
    c.0
    @54
    wcel
    #
    @27
    wn
    #
    @53
    @54
    @15
    wcel
    @56
    @25
    cI
    @15
    @26
    cS
    wph
    cI
    @15
    cS
    wf
    @1
    @24
    @18
    ad2antrr
    ffvelrnda
    @54
    cG
    c.0
    dmdprdsplitlem.0
    subg0cl
    syl
    adantr
    ifclda
    @25
    @30
    cvv
    wcel
    #
    @30
    wfun
    #
    @4
    c.0
    cfsupp
    wbr
    @30
    c.0
    csupp
    co
    @4
    c.0
    csupp
    co
    #
    wss
    @30
    c.0
    cfsupp
    wbr
    wph
    @58
    @1
    @24
    wph
    @48
    @58
    @49
    vn
    cI
    @29
    cvv
    mptexg
    syl
    ad2antrr
    @59
    @25
    vn
    cI
    @29
    funmpt
    a1i
    @25
    @8
    vh
    vi
    @4
    cG
    cA
    @9
    c.0
    @21
    @39
    @40
    @41
    dprdffsupp
    @25
    cI
    @29
    vn
    cvv
    @60
    c.0
    @25
    @26
    cI
    @60
    cdif
    wcel
    #
    wa
    #
    @29
    @27
    c.0
    c.0
    cif
    c.0
    @62
    @27
    @28
    c.0
    c.0
    @62
    @27
    @26
    cA
    @60
    cdif
    wcel
    #
    @28
    c.0
    wceq
    #
    @62
    @27
    wa
    @26
    cA
    @60
    @62
    @27
    simpr
    @61
    @26
    @60
    wcel
    wn
    @25
    @27
    @26
    cI
    @60
    eldifn
    ad2antlr
    eldifd
    @25
    @63
    @64
    @61
    @25
    cA
    @38
    cvv
    @4
    cvv
    @60
    @26
    c.0
    @43
    @60
    @60
    wss
    @25
    @60
    ssid
    a1i
    wph
    cA
    cvv
    wcel
    @1
    @24
    wph
    cA
    cI
    cvv
    @49
    dmdprdsplitlem.3
    ssexd
    ad2antrr
    c.0
    cvv
    wcel
    @25
    c.0
    cG
    c0g
    cfv
    cvv
    dmdprdsplitlem.0
    cG
    c0g
    fvex
    eqeltri
    #
    a1i
    suppssr
    adantlr
    syldan
    ifeq1da
    @27
    c.0
    ifid
    syl6eq
    @50
    suppss2
    @4
    @30
    cvv
    c.0
    fsuppsssupp
    syl22anc
    #
    dprdwd
    #
    @42
    dprdff
    @25
    cS
    vh
    vi
    @30
    cG
    cI
    cW
    c.0
    @44
    dmdprdsplitlem.w
    @47
    @51
    @67
    @45
    dprdfcntz
    @25
    cI
    @29
    vn
    cvv
    cA
    c.0
    @25
    @26
    @0
    wcel
    #
    wa
    @27
    @28
    c.0
    @68
    @57
    @25
    @26
    cI
    cA
    eldifn
    adantl
    iffalsed
    @50
    suppss2
    @66
    gsumzres
    3eqtrd
    @25
    cS
    vh
    vi
    cF
    cG
    @30
    cI
    cW
    c.0
    dmdprdsplitlem.0
    dmdprdsplitlem.w
    @47
    @51
    wph
    cF
    cW
    wcel
    @1
    @24
    dmdprdsplitlem.4
    ad2antrr
    @67
    dprdf11
    mpbid
    fveq1d
    @25
    cX
    cI
    wcel
    #
    @31
    @34
    wceq
    @1
    @69
    wph
    @24
    cX
    cI
    cA
    eldifi
    ad2antlr
    vn
    cX
    @29
    @34
    cI
    @30
    @26
    cX
    wceq
    @27
    @32
    @28
    @33
    c.0
    @26
    cX
    cA
    eleq1
    @26
    cX
    @4
    fveq2
    ifbieq1d
    @30
    eqid
    @27
    @28
    c.0
    @26
    @4
    fvex
    @65
    ifex
    fvmpt3i
    syl
    @25
    @32
    @33
    c.0
    @1
    @32
    wn
    wph
    @24
    cX
    cI
    cA
    eldifn
    ad2antlr
    iffalsed
    3eqtrd
    rexlimddv
end
