include "cgsu.mm"
include "co.mm"
include "wceq.mm"
include "cmpt.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cbs.mm"
include "eqid.mm"
include "dprdff.mm"
include "feqmptd.mm"
include "adantr.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cuni.mm"
include "csubg.mm"
include "cmrc.mm"
include "cin.mm"
include "dprdfcl.mm"
include "adantlr.mm"
include "cif.mm"
include "csg.mm"
include "cof.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "dprdfid.mm"
include "simpld.mm"
include "dprdfsub.mm"
include "simprd.mm"
include "cvv.mm"
include "dprddomcld.mm"
include "fvex.mm"
include "c0g.mm"
include "eqeltri.mm"
include "ifex.mm"
include "a1i.mm"
include "fvexd.mm"
include "eqidd.mm"
include "wf.mm"
include "offval2.mm"
include "oveq2d.mm"
include "simplr.mm"
include "oveq12d.mm"
include "cgrp.mm"
include "dprdgrp.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "grpsubid1.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"
include "ccntz.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "3syl.mm"
include "csubmnd.mm"
include "cmre.mm"
include "wss.mm"
include "cacs.mm"
include "subgacs.mm"
include "acsmre.mm"
include "cpw.mm"
include "crn.mm"
include "imassrn.mm"
include "dprdf2.mm"
include "frn.mm"
include "mresspw.mm"
include "sstrd.mm"
include "syl5ss.mm"
include "sspwuni.mm"
include "sylib.mm"
include "mrccl.mm"
include "subgsubm.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "fveq2d.mm"
include "grpsubid.mm"
include "subg0cl.mm"
include "eqeltrd.mm"
include "wn.mm"
include "mrcssidd.mm"
include "wfn.mm"
include "ffn.mm"
include "difssd.mm"
include "wne.mm"
include "df-ne.mm"
include "eldifsn.mm"
include "biimpri.mm"
include "sylan2br.mm"
include "adantll.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "elunii.mm"
include "sseldd.mm"
include "subgsubcl.mm"
include "ifbothda.mm"
include "fmptd.mm"
include "eqeltrrd.mm"
include "dprdfcntz.mm"
include "dprdffsupp.mm"
include "gsumzsubmcl.mm"
include "elind.mm"
include "dprddisj.mm"
include "eleqtrd.mm"
include "elsni.mm"
include "mpteq2dva.mm"
include "ex.mm"
include "gsumz.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem dprdfeq0
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let vh: setvar h
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cI: class I
  let cW: class W
  let c.0: class .0.
  let c.mi: class .-
  let vk: setvar k
  let c.pl: class .+
  let vn: setvar n
  let cA: class A
  let vf: setvar f
  let vy: setvar y
  let cH: class H
  let cN: class N
  let cX: class X
  assume eldprdi.0: |- .0. = ( 0g ` G )
  assume eldprdi.w: |- W = { h e. X_ i e. I ( S ` i ) | h finSupp .0. }
  assume eldprdi.1: |- ( ph -> G dom DProd S )
  assume eldprdi.2: |- ( ph -> dom S = I )
  assume eldprdi.3: |- ( ph -> F e. W )

  disjoint h x
  disjoint F h
  disjoint F x
  disjoint h i
  disjoint G h
  disjoint i x
  disjoint G i
  disjoint G x
  disjoint I h
  disjoint I i
  disjoint I x
  disjoint ph x
  disjoint .0. h
  disjoint .0. x
  disjoint S h
  disjoint S i
  disjoint S x
  disjoint .- k
  disjoint h k
  disjoint .+ h
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
  disjoint F y
  disjoint H h
  disjoint H k
  disjoint H x
  disjoint H y
  disjoint f i
  disjoint f n
  disjoint G f
  disjoint i k
  disjoint i n
  disjoint i y
  disjoint k n
  disjoint G k
  disjoint n x
  disjoint n y
  disjoint G n
  disjoint G y
  disjoint I f
  disjoint I k
  disjoint I n
  disjoint I y
  disjoint N h
  disjoint N x
  disjoint k ph
  disjoint n ph
  disjoint ph y
  disjoint .0. k
  disjoint .0. n
  disjoint .0. y
  disjoint S f
  disjoint S n
  disjoint S y
  disjoint W f
  disjoint X h
  disjoint X n
  assert |- ( ph -> ( ( G gsum F ) = .0. <-> F = ( x e. I |-> .0. ) ) )

  proof
    wph
    cG
    cF
    cgsu
    co
    #
    c.0
    wceq
    #
    cF
    vx
    cI
    c.0
    cmpt
    #
    wceq
    #
    wph
    @1
    @3
    wph
    @1
    wa
    #
    cF
    vx
    cI
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    @2
    wph
    cF
    @7
    wceq
    @1
    wph
    vx
    cI
    cG
    cbs
    cfv
    #
    cF
    wph
    @8
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
    @8
    eqid
    #
    dprdff
    #
    feqmptd
    adantr
    @4
    vx
    cI
    @6
    c.0
    @4
    @5
    cI
    wcel
    #
    wa
    #
    @6
    c.0
    csn
    #
    wcel
    @6
    c.0
    wceq
    @12
    @6
    @5
    cS
    cfv
    #
    cS
    cI
    @5
    csn
    #
    cdif
    #
    cima
    #
    cuni
    #
    cG
    csubg
    cfv
    #
    cmrc
    cfv
    #
    cfv
    #
    cin
    @13
    @12
    @14
    @21
    @6
    wph
    @11
    @6
    @14
    wcel
    @1
    wph
    cS
    vh
    vi
    cF
    cG
    cI
    cW
    @5
    c.0
    eldprdi.w
    eldprdi.1
    eldprdi.2
    eldprdi.3
    dprdfcl
    adantlr
    #
    @12
    cG
    vy
    cI
    vy
    cv
    #
    @5
    wceq
    #
    @6
    c.0
    cif
    #
    @23
    cF
    cfv
    #
    cG
    csg
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @6
    @21
    @12
    cG
    vy
    cI
    @25
    cmpt
    #
    cF
    @27
    cof
    co
    #
    cgsu
    co
    #
    cG
    @31
    cgsu
    co
    #
    @0
    @27
    co
    #
    @30
    @6
    @12
    @32
    cW
    wcel
    #
    @33
    @35
    wceq
    #
    @12
    cS
    vh
    vi
    @31
    cG
    cF
    cI
    @27
    cW
    c.0
    eldprdi.0
    eldprdi.w
    wph
    cG
    cS
    cdprd
    cdm
    wbr
    #
    @1
    @11
    eldprdi.1
    ad2antrr
    #
    wph
    cS
    cdm
    cI
    wceq
    @1
    @11
    eldprdi.2
    ad2antrr
    #
    @12
    @31
    cW
    wcel
    #
    @34
    @6
    wceq
    #
    @12
    @6
    cS
    vh
    vi
    vy
    @31
    cG
    cI
    cW
    @5
    c.0
    eldprdi.0
    eldprdi.w
    @39
    @40
    @4
    @11
    simpr
    #
    @22
    @31
    eqid
    dprdfid
    #
    simpld
    wph
    cF
    cW
    wcel
    @1
    @11
    eldprdi.3
    ad2antrr
    #
    @27
    eqid
    #
    dprdfsub
    #
    simprd
    @12
    @32
    @29
    cG
    cgsu
    @12
    vy
    cI
    @25
    @26
    @27
    @31
    cF
    cvv
    cvv
    cvv
    wph
    cI
    cvv
    wcel
    #
    @1
    @11
    wph
    cS
    cG
    cI
    eldprdi.1
    eldprdi.2
    dprddomcld
    #
    ad2antrr
    #
    @25
    cvv
    wcel
    @12
    @23
    cI
    wcel
    #
    wa
    #
    @24
    @6
    c.0
    @5
    cF
    fvex
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
    ifex
    a1i
    @52
    @23
    cF
    fvexd
    @12
    @31
    eqidd
    @12
    vy
    cI
    @8
    cF
    wph
    cI
    @8
    cF
    wf
    @1
    @11
    @10
    ad2antrr
    #
    feqmptd
    offval2
    #
    oveq2d
    @12
    @35
    @6
    c.0
    @27
    co
    #
    @6
    @12
    @34
    @6
    @0
    c.0
    @27
    @12
    @41
    @42
    @44
    simprd
    wph
    @1
    @11
    simplr
    oveq12d
    @12
    cG
    cgrp
    wcel
    #
    @6
    @8
    wcel
    #
    @55
    @6
    wceq
    @12
    @38
    @56
    @39
    cS
    cG
    dprdgrp
    #
    syl
    #
    @12
    cI
    @8
    @5
    cF
    @53
    @43
    ffvelrnd
    #
    @8
    cG
    @27
    @6
    c.0
    @9
    eldprdi.0
    @46
    grpsubid1
    syl2anc
    eqtrd
    3eqtr3d
    @12
    cI
    @21
    @29
    cG
    cvv
    c.0
    cG
    ccntz
    cfv
    #
    eldprdi.0
    @61
    eqid
    #
    wph
    cG
    cmnd
    wcel
    #
    @1
    @11
    wph
    @38
    @56
    @63
    eldprdi.1
    @58
    cG
    grpmnd
    3syl
    #
    ad2antrr
    @50
    @12
    @21
    @19
    wcel
    #
    @21
    cG
    csubmnd
    cfv
    wcel
    @12
    @19
    @8
    cmre
    cfv
    wcel
    #
    @18
    @8
    wss
    #
    @65
    @12
    @56
    @19
    @8
    cacs
    cfv
    wcel
    @66
    @59
    @8
    cG
    @9
    subgacs
    @19
    @8
    acsmre
    3syl
    #
    @12
    @17
    @8
    cpw
    #
    wss
    @67
    @12
    @17
    cS
    crn
    #
    @69
    cS
    @16
    imassrn
    @12
    @70
    @19
    @69
    @12
    cI
    @19
    cS
    wf
    #
    @70
    @19
    wss
    wph
    @71
    @1
    @11
    wph
    cS
    cG
    cI
    eldprdi.1
    eldprdi.2
    dprdf2
    ad2antrr
    #
    cI
    @19
    cS
    frn
    syl
    @12
    @66
    @19
    @69
    wss
    @68
    @19
    @8
    mresspw
    syl
    sstrd
    syl5ss
    @17
    @8
    sspwuni
    sylib
    #
    @19
    @18
    @20
    @8
    @20
    eqid
    #
    mrccl
    syl2anc
    #
    @21
    cG
    subgsubm
    syl
    @12
    vy
    cI
    @28
    @21
    @29
    @24
    @6
    @26
    @27
    co
    #
    @21
    wcel
    c.0
    @26
    @27
    co
    #
    @21
    wcel
    #
    @28
    @21
    wcel
    @52
    @6
    c.0
    @6
    @25
    wceq
    @76
    @28
    @21
    @6
    @25
    @26
    @27
    oveq1
    eleq1d
    c.0
    @25
    wceq
    @77
    @28
    @21
    c.0
    @25
    @26
    @27
    oveq1
    eleq1d
    @52
    @24
    wa
    #
    @76
    @6
    @6
    @27
    co
    #
    @21
    @79
    @26
    @6
    @6
    @27
    @79
    @23
    @5
    cF
    @52
    @24
    simpr
    fveq2d
    oveq2d
    @12
    @80
    @21
    wcel
    @51
    @24
    @12
    @80
    c.0
    @21
    @12
    @56
    @57
    @80
    c.0
    wceq
    @59
    @60
    @8
    cG
    @27
    @6
    c.0
    @9
    eldprdi.0
    @46
    grpsubid
    syl2anc
    @12
    @65
    c.0
    @21
    wcel
    #
    @75
    @21
    cG
    c.0
    eldprdi.0
    subg0cl
    #
    syl
    eqeltrd
    ad2antrr
    eqeltrd
    @52
    @24
    wn
    #
    wa
    #
    @65
    @81
    @26
    @21
    wcel
    @78
    @12
    @65
    @51
    @83
    @75
    ad2antrr
    #
    @84
    @65
    @81
    @85
    @82
    syl
    @84
    @18
    @21
    @26
    @12
    @18
    @21
    wss
    @51
    @83
    @12
    @19
    @18
    @20
    @8
    @68
    @74
    @73
    mrcssidd
    ad2antrr
    @84
    @26
    @23
    cS
    cfv
    #
    wcel
    #
    @86
    @17
    wcel
    #
    @26
    @18
    wcel
    @52
    @87
    @83
    @12
    cS
    vh
    vi
    cF
    cG
    cI
    cW
    @23
    c.0
    eldprdi.w
    @39
    @40
    @45
    dprdfcl
    adantr
    @84
    cS
    cI
    wfn
    #
    @16
    cI
    wss
    @23
    @16
    wcel
    #
    @88
    @12
    @89
    @51
    @83
    @12
    @71
    @89
    @72
    cI
    @19
    cS
    ffn
    syl
    ad2antrr
    @84
    cI
    @15
    difssd
    @51
    @83
    @90
    @12
    @83
    @51
    @23
    @5
    wne
    #
    @90
    @23
    @5
    df-ne
    @90
    @51
    @91
    wa
    @23
    cI
    @5
    eldifsn
    biimpri
    sylan2br
    adantll
    cI
    @16
    cS
    @23
    fnfvima
    syl3anc
    @26
    @86
    @17
    elunii
    syl2anc
    sseldd
    @21
    cG
    @27
    c.0
    @26
    @46
    subgsubcl
    syl3anc
    ifbothda
    @29
    eqid
    fmptd
    @12
    cS
    vh
    vi
    @29
    cG
    cI
    cW
    c.0
    @61
    eldprdi.w
    @39
    @40
    @12
    @32
    @29
    cW
    @54
    @12
    @36
    @37
    @47
    simpld
    eqeltrrd
    #
    @62
    dprdfcntz
    @12
    cS
    vh
    vi
    @29
    cG
    cI
    cW
    c.0
    eldprdi.w
    @39
    @40
    @92
    dprdffsupp
    gsumzsubmcl
    eqeltrrd
    elind
    @12
    cS
    cG
    cI
    @20
    @5
    c.0
    @39
    @40
    @43
    eldprdi.0
    @74
    dprddisj
    eleqtrd
    @6
    c.0
    elsni
    syl
    mpteq2dva
    eqtrd
    ex
    wph
    @1
    @3
    cG
    @2
    cgsu
    co
    #
    c.0
    wceq
    #
    wph
    @63
    @48
    @94
    @64
    @49
    cI
    vx
    cG
    cvv
    c.0
    eldprdi.0
    gsumz
    syl2anc
    @3
    @0
    @93
    c.0
    cF
    @2
    cG
    cgsu
    oveq2
    eqeq1d
    syl5ibrcom
    impbid
end
