include "cv.mm"
include "cgsu.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "cmpt.mm"
include "wcel.mm"
include "wa.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "wrex.mm"
include "wb.mm"
include "eldprd.mm"
include "syl.mm"
include "mpbid.mm"
include "simprd.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "dpjf.mm"
include "ffvelrnd.mm"
include "cvv.mm"
include "wfun.mm"
include "cfsupp.mm"
include "csupp.mm"
include "wss.mm"
include "dprddomcld.mm"
include "mptexg.mm"
include "funmpt.mm"
include "a1i.mm"
include "simprl.mm"
include "dprdffsupp.mm"
include "cdif.mm"
include "csn.mm"
include "cres.mm"
include "cpj1.mm"
include "eldifi.mm"
include "eqid.mm"
include "dpjval.mm"
include "fveq1d.mm"
include "sylan2.mm"
include "simplrr.mm"
include "cbs.mm"
include "ccntz.mm"
include "cmnd.mm"
include "cgrp.mm"
include "dprdgrp.mm"
include "grpmnd.mm"
include "3syl.mm"
include "wf.mm"
include "dprdff.mm"
include "crn.mm"
include "dprdfcntz.mm"
include "snssi.mm"
include "adantl.mm"
include "difss2d.mm"
include "suppssdm.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "ssconb.mm"
include "syl2anc.mm"
include "gsumzres.mm"
include "eqtr4d.mm"
include "cixp.mm"
include "crab.mm"
include "difss.mm"
include "dprdres.mm"
include "simpld.mm"
include "csubg.mm"
include "dprdf2.mm"
include "fssres.mm"
include "sylancl.mm"
include "feqmptd.mm"
include "reseq1d.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "dprdfcl.mm"
include "fvres.mm"
include "eleqtrrd.mm"
include "difexg.mm"
include "ssdif.mm"
include "sseli.mm"
include "ssid.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "suppssr.mm"
include "suppss2.mm"
include "fsuppsssupp.mm"
include "syl22anc.mm"
include "dprdwd.mm"
include "eqeltrd.mm"
include "eldprdi.mm"
include "cplusg.mm"
include "clsm.mm"
include "dprdsubg.mm"
include "dpjdisj.mm"
include "dpjcntz.mm"
include "pj1rid.mm"
include "sylanl2.mm"
include "mpdan.mm"
include "eqtrd.mm"
include "simprr.mm"
include "cin.mm"
include "c0.mm"
include "disjdif.mm"
include "cun.mm"
include "undif2.mm"
include "snssd.mm"
include "ssequn1.mm"
include "sylib.mm"
include "syl5req.mm"
include "gsumzsplit.mm"
include "feqresmpt.mm"
include "oveq2d.mm"
include "fveq2.mm"
include "gsumsn.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "dpjlsm.mm"
include "eleqtrd.mm"
include "pj1eq.mm"
include "mpteq2dva.mm"
include "jca.mm"
include "rexlimddv.mm"

theorem dpjidcl
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cP: class P
  let cS: class S
  let vh: setvar h
  let vi: setvar i
  let cG: class G
  let cI: class I
  let cW: class W
  let c.0: class .0.
  let vk: setvar k
  let vf: setvar f
  let vg: setvar g
  let vs: setvar s
  let cC: class C
  let cQ: class Q
  let cX: class X
  let cY: class Y
  assume dpjfval.1: |- ( ph -> G dom DProd S )
  assume dpjfval.2: |- ( ph -> dom S = I )
  assume dpjfval.p: |- P = ( G dProj S )
  assume dpjidcl.3: |- ( ph -> A e. ( G DProd S ) )
  assume dpjidcl.0: |- .0. = ( 0g ` G )
  assume dpjidcl.w: |- W = { h e. X_ i e. I ( S ` i ) | h finSupp .0. }

  disjoint h x
  disjoint .0. h
  disjoint .0. x
  disjoint h i
  disjoint G h
  disjoint i x
  disjoint G i
  disjoint G x
  disjoint P h
  disjoint P x
  disjoint i ph
  disjoint ph x
  disjoint I h
  disjoint I i
  disjoint I x
  disjoint W x
  disjoint A h
  disjoint A x
  disjoint S h
  disjoint S i
  disjoint S x
  disjoint h k
  disjoint k x
  disjoint .0. k
  disjoint f g
  disjoint f h
  disjoint f i
  disjoint f k
  disjoint f s
  disjoint f x
  disjoint G f
  disjoint g h
  disjoint g i
  disjoint g k
  disjoint g s
  disjoint g x
  disjoint G g
  disjoint h s
  disjoint i k
  disjoint i s
  disjoint k s
  disjoint G k
  disjoint s x
  disjoint G s
  disjoint P f
  disjoint f ph
  disjoint g ph
  disjoint k ph
  disjoint ph s
  disjoint C h
  disjoint I f
  disjoint I g
  disjoint I k
  disjoint I s
  disjoint Q g
  disjoint Q s
  disjoint Q x
  disjoint W f
  disjoint W k
  disjoint X h
  disjoint X x
  disjoint A f
  disjoint A k
  disjoint S f
  disjoint S g
  disjoint S k
  disjoint S s
  disjoint Y x
  assert |- ( ph -> ( ( x e. I |-> ( ( P ` x ) ` A ) ) e. W /\ A = ( G gsum ( x e. I |-> ( ( P ` x ) ` A ) ) ) ) )

  proof
    wph
    cA
    cG
    vf
    cv
    #
    cgsu
    co
    #
    wceq
    #
    vx
    cI
    cA
    vx
    cv
    #
    cP
    cfv
    #
    cfv
    #
    cmpt
    #
    cW
    wcel
    #
    cA
    cG
    @6
    cgsu
    co
    #
    wceq
    #
    wa
    vf
    cW
    wph
    cG
    cS
    cdprd
    cdm
    #
    wbr
    #
    @2
    vf
    cW
    wrex
    #
    wph
    cA
    cG
    cS
    cdprd
    co
    #
    wcel
    #
    @11
    @12
    wa
    #
    dpjidcl.3
    wph
    cS
    cdm
    cI
    wceq
    #
    @14
    @15
    wb
    dpjfval.2
    cA
    cS
    vf
    vh
    vi
    cG
    cI
    cW
    c.0
    dpjidcl.0
    dpjidcl.w
    eldprd
    syl
    mpbid
    simprd
    wph
    @0
    cW
    wcel
    #
    @2
    wa
    #
    wa
    #
    @7
    @9
    @19
    vx
    @5
    cS
    vh
    vi
    cG
    cI
    cW
    c.0
    dpjidcl.w
    wph
    @11
    @18
    dpjfval.1
    adantr
    #
    wph
    @16
    @18
    dpjfval.2
    adantr
    #
    @19
    @3
    cI
    wcel
    #
    wa
    #
    @13
    @3
    cS
    cfv
    #
    cA
    @4
    @23
    cP
    cS
    cG
    cI
    @3
    wph
    @11
    @18
    @22
    dpjfval.1
    ad2antrr
    #
    wph
    @16
    @18
    @22
    dpjfval.2
    ad2antrr
    #
    dpjfval.p
    @19
    @22
    simpr
    #
    dpjf
    wph
    @14
    @18
    @22
    dpjidcl.3
    ad2antrr
    #
    ffvelrnd
    @19
    @6
    cvv
    wcel
    #
    @6
    wfun
    #
    @0
    c.0
    cfsupp
    wbr
    #
    @6
    c.0
    csupp
    co
    @0
    c.0
    csupp
    co
    #
    wss
    @6
    c.0
    cfsupp
    wbr
    wph
    @29
    @18
    wph
    cI
    cvv
    wcel
    #
    @29
    wph
    cS
    cG
    cI
    dpjfval.1
    dpjfval.2
    dprddomcld
    #
    vx
    cI
    @5
    cvv
    mptexg
    syl
    adantr
    @30
    @19
    vx
    cI
    @5
    funmpt
    a1i
    @19
    cS
    vh
    vi
    @0
    cG
    cI
    cW
    c.0
    dpjidcl.w
    @20
    @21
    wph
    @17
    @2
    simprl
    #
    dprdffsupp
    #
    @19
    cI
    @5
    vx
    cvv
    @32
    c.0
    @19
    @3
    cI
    @32
    cdif
    #
    wcel
    #
    wa
    #
    @5
    cA
    @24
    cG
    cS
    cI
    @3
    csn
    #
    cdif
    #
    cres
    #
    cdprd
    co
    #
    cG
    cpj1
    cfv
    #
    co
    #
    cfv
    #
    c.0
    @38
    @19
    @22
    @5
    @46
    wceq
    @3
    cI
    @32
    eldifi
    #
    @23
    cA
    @4
    @45
    @23
    cP
    @44
    cS
    cG
    cI
    @3
    @25
    @26
    dpjfval.p
    @44
    eqid
    #
    @27
    dpjval
    fveq1d
    #
    sylan2
    @39
    cA
    @43
    wcel
    #
    @46
    c.0
    wceq
    #
    @39
    cA
    cG
    @0
    @41
    cres
    #
    cgsu
    co
    #
    @43
    @39
    cA
    @1
    @53
    wph
    @17
    @2
    @38
    simplrr
    @39
    cI
    cG
    cbs
    cfv
    #
    @0
    cG
    cvv
    @41
    c.0
    cG
    ccntz
    cfv
    #
    @54
    eqid
    #
    dpjidcl.0
    @55
    eqid
    #
    @19
    cG
    cmnd
    wcel
    #
    @38
    @19
    @11
    cG
    cgrp
    wcel
    #
    @58
    @20
    cS
    cG
    dprdgrp
    #
    cG
    grpmnd
    #
    3syl
    adantr
    wph
    @33
    @18
    @38
    @34
    ad2antrr
    @19
    cI
    @54
    @0
    wf
    #
    @38
    @19
    @54
    cS
    vh
    vi
    @0
    cG
    cI
    cW
    c.0
    dpjidcl.w
    @20
    @21
    @35
    @56
    dprdff
    #
    adantr
    @38
    @19
    @22
    @0
    crn
    #
    @64
    @55
    cfv
    wss
    @47
    @23
    cS
    vh
    vi
    @0
    cG
    cI
    cW
    c.0
    @55
    dpjidcl.w
    @25
    @26
    @19
    @17
    @22
    @35
    adantr
    #
    @57
    dprdfcntz
    #
    sylan2
    @39
    @40
    @37
    wss
    #
    @32
    @41
    wss
    #
    @38
    @67
    @19
    @3
    @37
    snssi
    adantl
    #
    @39
    @40
    cI
    wss
    #
    @32
    cI
    wss
    #
    @67
    @68
    wb
    @39
    @40
    cI
    @32
    @69
    difss2d
    @19
    @71
    @38
    @19
    @0
    cdm
    #
    @32
    cI
    @0
    c.0
    suppssdm
    @19
    @62
    @72
    cI
    wceq
    @63
    cI
    @54
    @0
    fdm
    syl
    syl5sseq
    adantr
    @40
    @32
    cI
    ssconb
    syl2anc
    mpbid
    @19
    @31
    @38
    @36
    adantr
    gsumzres
    eqtr4d
    @38
    @19
    @22
    @53
    @43
    wcel
    @47
    @23
    @42
    vh
    vi
    @52
    cG
    @41
    vh
    cv
    c.0
    cfsupp
    wbr
    vh
    vi
    @41
    vi
    cv
    @42
    cfv
    cixp
    crab
    #
    c.0
    dpjidcl.0
    @73
    eqid
    #
    @23
    cG
    @42
    @10
    wbr
    #
    @43
    @13
    wss
    @23
    @41
    cS
    cG
    cI
    @25
    @26
    @41
    cI
    wss
    #
    @23
    cI
    @40
    difss
    #
    a1i
    dprdres
    simpld
    #
    @23
    @41
    cG
    csubg
    cfv
    #
    @42
    wf
    #
    @42
    cdm
    @41
    wceq
    @23
    cI
    @79
    cS
    wf
    @76
    @80
    @23
    cS
    cG
    cI
    @25
    @26
    dprdf2
    #
    @77
    cI
    @79
    @41
    cS
    fssres
    sylancl
    @41
    @79
    @42
    fdm
    syl
    #
    @23
    @52
    vk
    @41
    vk
    cv
    #
    @0
    cfv
    #
    cmpt
    #
    @73
    @23
    @52
    vk
    cI
    @84
    cmpt
    #
    @41
    cres
    #
    @85
    @23
    @0
    @86
    @41
    @23
    vk
    cI
    @54
    @0
    @19
    @62
    @22
    @63
    adantr
    #
    feqmptd
    reseq1d
    @76
    @87
    @85
    wceq
    @77
    vk
    cI
    @41
    @84
    resmpt
    ax-mp
    syl6eq
    @23
    vk
    @84
    @42
    vh
    vi
    cG
    @41
    @73
    c.0
    @74
    @78
    @82
    @23
    @83
    @41
    wcel
    #
    wa
    @84
    @83
    cS
    cfv
    #
    @83
    @42
    cfv
    #
    @89
    @23
    @83
    cI
    wcel
    @84
    @90
    wcel
    @83
    cI
    @40
    eldifi
    @23
    cS
    vh
    vi
    @0
    cG
    cI
    cW
    @83
    c.0
    dpjidcl.w
    @25
    @26
    @65
    dprdfcl
    sylan2
    @89
    @91
    @90
    wceq
    @23
    @83
    @41
    cS
    fvres
    adantl
    eleqtrrd
    @23
    @85
    cvv
    wcel
    #
    @85
    wfun
    #
    @31
    @85
    c.0
    csupp
    co
    @32
    wss
    @85
    c.0
    cfsupp
    wbr
    wph
    @92
    @18
    @22
    wph
    @41
    cvv
    wcel
    #
    @92
    wph
    @33
    @94
    @34
    cI
    @40
    cvv
    difexg
    syl
    #
    vk
    @41
    @84
    cvv
    mptexg
    syl
    ad2antrr
    @93
    @23
    vk
    @41
    @84
    funmpt
    a1i
    @19
    @31
    @22
    @36
    adantr
    @23
    @41
    @84
    vk
    cvv
    @32
    c.0
    @83
    @41
    @32
    cdif
    #
    wcel
    @23
    @83
    @37
    wcel
    @84
    c.0
    wceq
    @96
    @37
    @83
    @76
    @96
    @37
    wss
    @77
    @41
    cI
    @32
    ssdif
    ax-mp
    sseli
    @23
    cI
    @54
    cvv
    @0
    cvv
    @32
    @83
    c.0
    @88
    @32
    @32
    wss
    @23
    @32
    ssid
    a1i
    wph
    @33
    @18
    @22
    @34
    ad2antrr
    #
    c.0
    cvv
    wcel
    @23
    c.0
    cG
    c0g
    cfv
    cvv
    dpjidcl.0
    cG
    c0g
    fvex
    eqeltri
    a1i
    suppssr
    sylan2
    wph
    @94
    @18
    @22
    @95
    ad2antrr
    suppss2
    @0
    @85
    cvv
    c.0
    fsuppsssupp
    syl22anc
    dprdwd
    eqeltrd
    eldprdi
    #
    sylan2
    eqeltrd
    @38
    @19
    @22
    @50
    @51
    @47
    @23
    @44
    cG
    cplusg
    cfv
    #
    cG
    clsm
    cfv
    #
    @24
    @43
    cG
    cA
    c.0
    @55
    @99
    eqid
    #
    @100
    eqid
    #
    dpjidcl.0
    @57
    @23
    cI
    @79
    @3
    cS
    @81
    @27
    ffvelrnd
    #
    @23
    @75
    @43
    @79
    wcel
    @78
    @42
    cG
    dprdsubg
    syl
    #
    @23
    cS
    cG
    cI
    @3
    c.0
    @25
    @26
    @27
    dpjidcl.0
    dpjdisj
    #
    @23
    cS
    cG
    cI
    @3
    @55
    @25
    @26
    @27
    @57
    dpjcntz
    #
    @48
    pj1rid
    sylanl2
    mpdan
    eqtrd
    wph
    @33
    @18
    @34
    adantr
    suppss2
    @0
    @6
    cvv
    c.0
    fsuppsssupp
    syl22anc
    dprdwd
    @19
    cA
    @1
    @8
    wph
    @17
    @2
    simprr
    @19
    @0
    @6
    cG
    cgsu
    @19
    @0
    vx
    cI
    @3
    @0
    cfv
    #
    cmpt
    @6
    @19
    vx
    cI
    @54
    @0
    @63
    feqmptd
    @19
    vx
    cI
    @5
    @107
    @23
    @5
    @46
    @107
    @49
    @23
    @46
    @107
    wceq
    #
    cA
    @43
    @24
    @44
    co
    cfv
    @53
    wceq
    #
    @23
    cA
    @107
    @53
    @99
    co
    #
    wceq
    @108
    @109
    wa
    @23
    cA
    @1
    cG
    @0
    @40
    cres
    #
    cgsu
    co
    #
    @53
    @99
    co
    @110
    wph
    @17
    @2
    @22
    simplrr
    @23
    cI
    @54
    @40
    @41
    @99
    @0
    cG
    cvv
    c.0
    @55
    @56
    dpjidcl.0
    @101
    @57
    @23
    @11
    @59
    @58
    @25
    @60
    @61
    3syl
    #
    @97
    @88
    @66
    @23
    cS
    vh
    vi
    @0
    cG
    cI
    cW
    c.0
    dpjidcl.w
    @25
    @26
    @65
    dprdffsupp
    @40
    @41
    cin
    c0
    wceq
    @23
    @40
    cI
    disjdif
    a1i
    @23
    @40
    @41
    cun
    @40
    cI
    cun
    #
    cI
    @40
    cI
    undif2
    @23
    @70
    @114
    cI
    wceq
    @23
    @3
    cI
    @27
    snssd
    #
    @40
    cI
    ssequn1
    sylib
    syl5req
    gsumzsplit
    @23
    @112
    @107
    @53
    @99
    @23
    @112
    cG
    vk
    @40
    @84
    cmpt
    #
    cgsu
    co
    #
    @107
    @23
    @111
    @116
    cG
    cgsu
    @23
    vk
    cI
    @54
    @40
    @0
    @88
    @115
    feqresmpt
    oveq2d
    @23
    @58
    @22
    @107
    @54
    wcel
    @117
    @107
    wceq
    @113
    @27
    @23
    cI
    @54
    @3
    @0
    @88
    @27
    ffvelrnd
    @84
    @54
    @107
    vk
    cG
    @3
    cI
    @56
    @83
    @3
    @0
    fveq2
    gsumsn
    syl3anc
    eqtrd
    oveq1d
    3eqtrd
    @23
    @107
    @53
    @44
    @99
    @100
    @24
    @43
    cG
    cA
    c.0
    @55
    @101
    @102
    dpjidcl.0
    @57
    @103
    @104
    @105
    @106
    @48
    @23
    cA
    @13
    @24
    @43
    @100
    co
    @28
    @23
    @100
    cS
    cG
    cI
    @3
    @25
    @26
    @27
    @102
    dpjlsm
    eleqtrd
    @19
    cS
    vh
    vi
    @0
    cG
    cI
    cW
    @3
    c.0
    dpjidcl.w
    @20
    @21
    @35
    dprdfcl
    @98
    pj1eq
    mpbid
    simpld
    eqtrd
    mpteq2dva
    eqtr4d
    oveq2d
    eqtrd
    jca
    rexlimddv
end
