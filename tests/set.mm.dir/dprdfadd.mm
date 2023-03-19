include "cof.mm"
include "co.mm"
include "wcel.mm"
include "cgsu.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cvv.mm"
include "dprddomcld.mm"
include "dprdfcl.mm"
include "cbs.mm"
include "eqid.mm"
include "dprdff.mm"
include "feqmptd.mm"
include "offval2.mm"
include "wa.mm"
include "csubg.mm"
include "dprdf2.mm"
include "ffvelrnda.mm"
include "subgcl.mm"
include "syl3anc.mm"
include "cfsupp.mm"
include "wbr.mm"
include "csupp.mm"
include "cfn.mm"
include "cun.mm"
include "wss.mm"
include "dprdffsupp.mm"
include "fsuppunfi.mm"
include "cdif.mm"
include "ssun1.mm"
include "a1i.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "suppssr.mm"
include "ssun2.mm"
include "oveq12d.mm"
include "cgrp.mm"
include "cdprd.mm"
include "cdm.mm"
include "dprdgrp.mm"
include "syl.mm"
include "grpidcl.mm"
include "grplid.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqtrd.mm"
include "suppss2.mm"
include "ssfi.mm"
include "wfun.mm"
include "wb.mm"
include "funmpt.mm"
include "mptexg.mm"
include "funisfsupp.mm"
include "mpbird.mm"
include "dprdwd.mm"
include "eqeltrd.mm"
include "ccntz.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "dprdfcntz.mm"
include "csn.mm"
include "cres.mm"
include "vex.mm"
include "csubmnd.mm"
include "wf.mm"
include "eldifi.mm"
include "adantl.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "snssd.mm"
include "cntzsubm.mm"
include "wfn.mm"
include "wral.mm"
include "ffn.mm"
include "simprl.mm"
include "fnssres.mm"
include "fvres.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "ffvelrnd.mm"
include "subgss.mm"
include "mpdan.mm"
include "cntz2ss.mm"
include "sselda.mm"
include "wn.mm"
include "wne.mm"
include "simpr.mm"
include "simplrr.mm"
include "eldifbd.mm"
include "nelne2.mm"
include "dprdcntz.mm"
include "sseldd.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "crn.mm"
include "resss.mm"
include "rnss.mm"
include "ax-mp.mm"
include "cntzidss.mm"
include "sylancl.mm"
include "fsuppres.mm"
include "gsumzsubmcl.mm"
include "fssresd.mm"
include "gsumzcl.mm"
include "cntzrec.mm"
include "mpbid.mm"
include "snss.mm"
include "sylibr.mm"
include "gsumzaddlem.mm"
include "jca.mm"

theorem dprdfadd
  let wph: wff ph
  let c.pl: class .+
  let cS: class S
  let vh: setvar h
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cW: class W
  let c.0: class .0.
  let c.mi: class .-
  let vk: setvar k
  let vx: setvar x
  let vn: setvar n
  let cA: class A
  let vf: setvar f
  let vy: setvar y
  let cN: class N
  let cX: class X
  assume eldprdi.0: |- .0. = ( 0g ` G )
  assume eldprdi.w: |- W = { h e. X_ i e. I ( S ` i ) | h finSupp .0. }
  assume eldprdi.1: |- ( ph -> G dom DProd S )
  assume eldprdi.2: |- ( ph -> dom S = I )
  assume eldprdi.3: |- ( ph -> F e. W )
  assume dprdfadd.4: |- ( ph -> H e. W )
  assume dprdfadd.b: |- .+ = ( +g ` G )

  disjoint .+ h
  disjoint F h
  disjoint H h
  disjoint h i
  disjoint G h
  disjoint G i
  disjoint I h
  disjoint I i
  disjoint .0. h
  disjoint S h
  disjoint S i
  disjoint .- k
  disjoint h k
  disjoint h x
  disjoint k x
  disjoint .+ k
  disjoint .+ x
  disjoint h n
  disjoint A h
  disjoint A n
  disjoint f h
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint h y
  disjoint k y
  disjoint F k
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint H k
  disjoint H x
  disjoint H y
  disjoint f i
  disjoint f n
  disjoint G f
  disjoint i k
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint k n
  disjoint G k
  disjoint n x
  disjoint n y
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint I f
  disjoint I k
  disjoint I n
  disjoint I x
  disjoint I y
  disjoint N h
  disjoint N x
  disjoint k ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint .0. k
  disjoint .0. n
  disjoint .0. x
  disjoint .0. y
  disjoint S f
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint W f
  disjoint X h
  disjoint X n
  assert |- ( ph -> ( ( F oF .+ H ) e. W /\ ( G gsum ( F oF .+ H ) ) = ( ( G gsum F ) .+ ( G gsum H ) ) ) )

  proof
    wph
    cF
    cH
    c.pl
    cof
    co
    #
    cW
    wcel
    cG
    @0
    cgsu
    co
    cG
    cF
    cgsu
    co
    cG
    cH
    cgsu
    co
    c.pl
    co
    wceq
    wph
    @0
    vx
    cI
    vx
    cv
    #
    cF
    cfv
    #
    @1
    cH
    cfv
    #
    c.pl
    co
    #
    cmpt
    #
    cW
    wph
    vx
    cI
    @2
    @3
    c.pl
    cF
    cH
    cvv
    @1
    cS
    cfv
    #
    @6
    wph
    cS
    cG
    cI
    eldprdi.1
    eldprdi.2
    dprddomcld
    #
    wph
    cS
    vh
    vi
    cF
    cG
    cI
    cW
    @1
    c.0
    eldprdi.w
    eldprdi.1
    eldprdi.2
    eldprdi.3
    dprdfcl
    #
    wph
    cS
    vh
    vi
    cH
    cG
    cI
    cW
    @1
    c.0
    eldprdi.w
    eldprdi.1
    eldprdi.2
    dprdfadd.4
    dprdfcl
    #
    wph
    vx
    cI
    cG
    cbs
    cfv
    #
    cF
    wph
    @10
    cS
    vh
    vi
    cF
    cG
    cI
    cW
    c.0
    eldprdi.w
    eldprdi.1
    eldprdi.2
    eldprdi.3
    @10
    eqid
    #
    dprdff
    #
    feqmptd
    wph
    vx
    cI
    @10
    cH
    wph
    @10
    cS
    vh
    vi
    cH
    cG
    cI
    cW
    c.0
    eldprdi.w
    eldprdi.1
    eldprdi.2
    dprdfadd.4
    @11
    dprdff
    #
    feqmptd
    offval2
    wph
    vx
    @4
    cS
    vh
    vi
    cG
    cI
    cW
    c.0
    eldprdi.w
    eldprdi.1
    eldprdi.2
    wph
    @1
    cI
    wcel
    wa
    @6
    cG
    csubg
    cfv
    #
    wcel
    @2
    @6
    wcel
    @3
    @6
    wcel
    @4
    @6
    wcel
    wph
    cI
    @14
    @1
    cS
    wph
    cS
    cG
    cI
    eldprdi.1
    eldprdi.2
    dprdf2
    ffvelrnda
    @8
    @9
    c.pl
    @6
    cG
    @2
    @3
    dprdfadd.b
    subgcl
    syl3anc
    wph
    @5
    c.0
    cfsupp
    wbr
    #
    @5
    c.0
    csupp
    co
    #
    cfn
    wcel
    #
    wph
    cF
    c.0
    csupp
    co
    #
    cH
    c.0
    csupp
    co
    #
    cun
    #
    cfn
    wcel
    @16
    @20
    wss
    @17
    wph
    cF
    cH
    c.0
    wph
    cS
    vh
    vi
    cF
    cG
    cI
    cW
    c.0
    eldprdi.w
    eldprdi.1
    eldprdi.2
    eldprdi.3
    dprdffsupp
    #
    wph
    cS
    vh
    vi
    cH
    cG
    cI
    cW
    c.0
    eldprdi.w
    eldprdi.1
    eldprdi.2
    dprdfadd.4
    dprdffsupp
    #
    fsuppunfi
    wph
    cI
    @4
    vx
    cvv
    @20
    c.0
    wph
    @1
    cI
    @20
    cdif
    wcel
    #
    wa
    #
    @4
    c.0
    c.0
    c.pl
    co
    #
    c.0
    @24
    @2
    c.0
    @3
    c.0
    c.pl
    wph
    cI
    @10
    cvv
    cF
    cvv
    @20
    @1
    c.0
    @12
    @18
    @20
    wss
    wph
    @18
    @19
    ssun1
    a1i
    @7
    c.0
    cvv
    wcel
    #
    wph
    c.0
    cG
    c0g
    cfv
    cvv
    eldprdi.0
    cG
    c0g
    fvex
    eqeltri
    a1i
    #
    suppssr
    wph
    cI
    @10
    cvv
    cH
    cvv
    @20
    @1
    c.0
    @13
    @19
    @20
    wss
    wph
    @19
    @18
    ssun2
    a1i
    @7
    @27
    suppssr
    oveq12d
    wph
    @25
    c.0
    wceq
    #
    @23
    wph
    cG
    cgrp
    wcel
    #
    c.0
    @10
    wcel
    #
    @28
    wph
    cG
    cS
    cdprd
    cdm
    wbr
    #
    @29
    eldprdi.1
    cS
    cG
    dprdgrp
    syl
    #
    wph
    @29
    @30
    @32
    @10
    cG
    c.0
    @11
    eldprdi.0
    grpidcl
    syl
    @10
    c.pl
    cG
    c.0
    c.0
    @11
    dprdfadd.b
    eldprdi.0
    grplid
    syl2anc
    adantr
    eqtrd
    @7
    suppss2
    @20
    @16
    ssfi
    syl2anc
    wph
    @5
    wfun
    #
    @5
    cvv
    wcel
    #
    @26
    @15
    @17
    wb
    @33
    wph
    vx
    cI
    @4
    funmpt
    a1i
    wph
    cI
    cvv
    wcel
    @34
    @7
    vx
    cI
    @4
    cvv
    mptexg
    syl
    @27
    @5
    cvv
    cvv
    c.0
    funisfsupp
    syl3anc
    mpbird
    dprdwd
    eqeltrd
    #
    wph
    vx
    cI
    @10
    c.pl
    vk
    cF
    cG
    cH
    cvv
    cF
    cH
    cun
    c.0
    csupp
    co
    #
    c.0
    cG
    ccntz
    cfv
    #
    @11
    eldprdi.0
    dprdfadd.b
    @37
    eqid
    #
    wph
    @29
    cG
    cmnd
    wcel
    #
    @32
    cG
    grpmnd
    syl
    #
    @7
    @21
    @22
    @36
    eqid
    @12
    @13
    wph
    cS
    vh
    vi
    cF
    cG
    cI
    cW
    c.0
    @37
    eldprdi.w
    eldprdi.1
    eldprdi.2
    eldprdi.3
    @38
    dprdfcntz
    wph
    cS
    vh
    vi
    cH
    cG
    cI
    cW
    c.0
    @37
    eldprdi.w
    eldprdi.1
    eldprdi.2
    dprdfadd.4
    @38
    dprdfcntz
    #
    wph
    cS
    vh
    vi
    @0
    cG
    cI
    cW
    c.0
    @37
    eldprdi.w
    eldprdi.1
    eldprdi.2
    @35
    @38
    dprdfcntz
    wph
    @1
    cI
    wss
    #
    vk
    cv
    #
    cI
    @1
    cdif
    wcel
    #
    wa
    #
    wa
    #
    @43
    cF
    cfv
    #
    csn
    #
    cG
    cH
    @1
    cres
    #
    cgsu
    co
    #
    csn
    #
    @37
    cfv
    #
    wss
    #
    @47
    @52
    wcel
    @46
    @51
    @48
    @37
    cfv
    #
    wss
    #
    @53
    @46
    @50
    @54
    @46
    @1
    @54
    @49
    cG
    cvv
    c.0
    @37
    eldprdi.0
    @38
    wph
    @39
    @45
    @40
    adantr
    #
    @1
    cvv
    wcel
    @46
    vx
    vex
    a1i
    #
    @46
    @39
    @48
    @10
    wss
    #
    @54
    cG
    csubmnd
    cfv
    wcel
    @56
    @46
    @47
    @10
    wph
    cI
    @10
    cF
    wf
    @43
    cI
    wcel
    #
    @47
    @10
    wcel
    @45
    @12
    @44
    @59
    @42
    @43
    cI
    @1
    eldifi
    adantl
    #
    cI
    @10
    @43
    cF
    ffvelrn
    syl2an
    snssd
    #
    @10
    @48
    cG
    @37
    @11
    @38
    cntzsubm
    syl2anc
    @46
    @49
    @1
    wfn
    #
    vy
    cv
    #
    @49
    cfv
    #
    @54
    wcel
    #
    vy
    @1
    wral
    @1
    @54
    @49
    wf
    @46
    cH
    cI
    wfn
    #
    @42
    @62
    @46
    cI
    @10
    cH
    wf
    #
    @66
    wph
    @67
    @45
    @13
    adantr
    #
    cI
    @10
    cH
    ffn
    syl
    wph
    @42
    @44
    simprl
    #
    cI
    @1
    cH
    fnssres
    syl2anc
    @46
    @65
    vy
    @1
    @46
    @63
    @1
    wcel
    #
    wa
    #
    @64
    @63
    cH
    cfv
    #
    @54
    @70
    @64
    @72
    wceq
    @46
    @63
    @1
    cH
    fvres
    adantl
    @71
    @43
    cS
    cfv
    #
    @37
    cfv
    #
    @54
    @72
    @71
    @73
    @10
    wss
    #
    @48
    @73
    wss
    @74
    @54
    wss
    @71
    @73
    @14
    wcel
    @75
    @71
    cI
    @14
    @43
    cS
    @71
    cS
    cG
    cI
    wph
    @31
    @45
    @70
    eldprdi.1
    ad2antrr
    #
    wph
    cS
    cdm
    cI
    wceq
    @45
    @70
    eldprdi.2
    ad2antrr
    #
    dprdf2
    @45
    @59
    wph
    @70
    @60
    ad2antlr
    #
    ffvelrnd
    @10
    @73
    cG
    @11
    subgss
    syl
    @71
    @47
    @73
    @71
    @59
    @47
    @73
    wcel
    @78
    @71
    cS
    vh
    vi
    cF
    cG
    cI
    cW
    @43
    c.0
    eldprdi.w
    @76
    @77
    wph
    cF
    cW
    wcel
    @45
    @70
    eldprdi.3
    ad2antrr
    dprdfcl
    mpdan
    snssd
    @10
    @73
    @48
    cG
    @37
    @11
    @38
    cntz2ss
    syl2anc
    @71
    @63
    cS
    cfv
    #
    @74
    @72
    @71
    cS
    cG
    cI
    @63
    @43
    @37
    @76
    @77
    @46
    @1
    cI
    @63
    @69
    sselda
    #
    @78
    @71
    @70
    @43
    @1
    wcel
    wn
    @63
    @43
    wne
    @46
    @70
    simpr
    @71
    @43
    cI
    @1
    wph
    @42
    @44
    @70
    simplrr
    eldifbd
    @63
    @43
    @1
    nelne2
    syl2anc
    @38
    dprdcntz
    @71
    @63
    cI
    wcel
    @72
    @79
    wcel
    @80
    @71
    cS
    vh
    vi
    cH
    cG
    cI
    cW
    @63
    c.0
    eldprdi.w
    @76
    @77
    wph
    cH
    cW
    wcel
    @45
    @70
    dprdfadd.4
    ad2antrr
    dprdfcl
    mpdan
    sseldd
    sseldd
    eqeltrd
    ralrimiva
    vy
    @1
    @54
    @49
    ffnfv
    sylanbrc
    wph
    @49
    crn
    #
    @81
    @37
    cfv
    wss
    #
    @45
    wph
    cH
    crn
    #
    @83
    @37
    cfv
    wss
    @81
    @83
    wss
    #
    @82
    @41
    @49
    cH
    wss
    @84
    cH
    @1
    resss
    @49
    cH
    rnss
    ax-mp
    @83
    @81
    cG
    @37
    @38
    cntzidss
    sylancl
    adantr
    #
    wph
    @49
    c.0
    cfsupp
    wbr
    @45
    wph
    cH
    cvv
    @1
    c.0
    @22
    @27
    fsuppres
    adantr
    #
    gsumzsubmcl
    snssd
    @46
    @51
    @10
    wss
    @58
    @55
    @53
    wb
    @46
    @50
    @10
    @46
    @1
    @10
    @49
    cG
    cvv
    c.0
    @37
    @11
    eldprdi.0
    @38
    @56
    @57
    @46
    cI
    @10
    @1
    cH
    @68
    @69
    fssresd
    @85
    @86
    gsumzcl
    snssd
    @61
    @10
    @51
    @48
    cG
    @37
    @11
    @38
    cntzrec
    syl2anc
    mpbid
    @47
    @52
    @43
    cF
    fvex
    snss
    sylibr
    gsumzaddlem
    jca
end
