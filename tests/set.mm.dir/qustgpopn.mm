include "ctgp.mm"
include "wcel.mm"
include "cnsg.mm"
include "cfv.mm"
include "w3a.mm"
include "cima.mm"
include "cqtop.mm"
include "co.mm"
include "cqg.mm"
include "cqs.mm"
include "wss.mm"
include "ccnv.mm"
include "crn.mm"
include "imassrn.mm"
include "wfo.mm"
include "wceq.mm"
include "cvv.mm"
include "cqus.mm"
include "a1i.mm"
include "cbs.mm"
include "ovex.mm"
include "simp1.mm"
include "quslem.mm"
include "forn.mm"
include "syl.mm"
include "syl5sseq.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "cec.mm"
include "cmpt.mm"
include "eceq1.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "mptpreima.mm"
include "rabeq2i.mm"
include "wfun.mm"
include "funmpt2.mm"
include "fvelima.mm"
include "mpan.mm"
include "cminusg.mm"
include "cplusg.mm"
include "wbr.mm"
include "ctopon.mm"
include "tgptopon.mm"
include "simp3.mm"
include "toponss.mm"
include "syl2anc.mm"
include "adantr.mm"
include "sselda.mm"
include "ecexg.mm"
include "ax-mp.mm"
include "fvmpt.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "csubg.mm"
include "wer.mm"
include "nsgsubg.mm"
include "3ad2ant2.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "eqger.mm"
include "simplr.mm"
include "erth.mm"
include "wb.mm"
include "subgss.mm"
include "eqgval.mm"
include "3bitr2d.mm"
include "ccn.mm"
include "chmeo.mm"
include "coppg.mm"
include "oppgplus.mm"
include "mpteq2i.mm"
include "oppgtgp.mm"
include "oppgbas.mm"
include "oppgtopn.mm"
include "tgplacthmeo.mm"
include "syl5eqelr.mm"
include "hmeocn.mm"
include "ad3antrrr.mm"
include "cnima.mm"
include "c0g.mm"
include "cgrp.mm"
include "tgpgrp.mm"
include "grprinv.mm"
include "oveq1d.mm"
include "grpinvcl.mm"
include "grpass.mm"
include "syl13anc.mm"
include "grplid.mm"
include "3eqtr3d.mm"
include "eqeltrd.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "crab.mm"
include "wfn.mm"
include "wi.mm"
include "fnmpti.mm"
include "fnfvima.mm"
include "3expia.mm"
include "sylancr.mm"
include "simpr.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "fvmpt3i.mm"
include "grplinv.mm"
include "mpbir3and.mm"
include "erthi.mm"
include "eqtr4d.mm"
include "sylibd.mm"
include "ss2rabdv.mm"
include "3sstr4g.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "3ad2antr3.mm"
include "ex.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "ctop.mm"
include "topontop.mm"
include "eltop2.mm"
include "3syl.mm"
include "mpbird.mm"
include "elqtop3.mm"
include "mpbir2and.mm"
include "qusval.mm"
include "imastopn.mm"
include "eleqtrrd.mm"

theorem qustgpopn
  let vx: setvar x
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vt: setvar t
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let c.mi: class .-
  assume qustgp.h: |- H = ( G /s ( G ~QG Y ) )
  assume qustgpopn.x: |- X = ( Base ` G )
  assume qustgpopn.j: |- J = ( TopOpen ` G )
  assume qustgpopn.k: |- K = ( TopOpen ` H )
  assume qustgpopn.f: |- F = ( x e. X |-> [ x ] ( G ~QG Y ) )

  disjoint G x
  disjoint J x
  disjoint S x
  disjoint X x
  disjoint H x
  disjoint K x
  disjoint Y x
  disjoint b t
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a p
  disjoint a q
  disjoint a r
  disjoint a s
  disjoint a u
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint G a
  disjoint b c
  disjoint b d
  disjoint b p
  disjoint b q
  disjoint b r
  disjoint b s
  disjoint b u
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint G b
  disjoint c d
  disjoint c p
  disjoint c q
  disjoint c r
  disjoint c s
  disjoint c u
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint G c
  disjoint d p
  disjoint d q
  disjoint d r
  disjoint d s
  disjoint d u
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint G d
  disjoint p q
  disjoint p r
  disjoint p s
  disjoint p u
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint G p
  disjoint q r
  disjoint q s
  disjoint q u
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint G q
  disjoint r s
  disjoint r u
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint G r
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint G s
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint a t
  disjoint J a
  disjoint c t
  disjoint J c
  disjoint d t
  disjoint J d
  disjoint p t
  disjoint J p
  disjoint q t
  disjoint J q
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint J t
  disjoint J u
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint F a
  disjoint F p
  disjoint F q
  disjoint F r
  disjoint F s
  disjoint F u
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint S a
  disjoint S u
  disjoint S y
  disjoint S z
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X p
  disjoint X q
  disjoint X u
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H d
  disjoint H p
  disjoint H q
  disjoint H r
  disjoint H s
  disjoint H u
  disjoint H w
  disjoint H y
  disjoint H z
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint K d
  disjoint K p
  disjoint K q
  disjoint K r
  disjoint K s
  disjoint K u
  disjoint K w
  disjoint K y
  disjoint K z
  disjoint .- c
  disjoint .- d
  disjoint .- p
  disjoint .- q
  disjoint .- t
  disjoint Y a
  disjoint Y b
  disjoint Y c
  disjoint Y d
  disjoint Y p
  disjoint Y q
  disjoint Y r
  disjoint Y s
  disjoint Y u
  disjoint Y w
  disjoint Y y
  disjoint Y z
  assert |- ( ( G e. TopGrp /\ Y e. ( NrmSGrp ` G ) /\ S e. J ) -> ( F " S ) e. K )

  proof
    cG
    ctgp
    wcel
    #
    cY
    cG
    cnsg
    cfv
    wcel
    #
    cS
    cJ
    wcel
    #
    w3a
    #
    cF
    cS
    cima
    #
    cJ
    cF
    cqtop
    co
    #
    cK
    @3
    @4
    @5
    wcel
    #
    @4
    cX
    cG
    cY
    cqg
    co
    #
    cqs
    #
    wss
    #
    cF
    ccnv
    @4
    cima
    #
    cJ
    wcel
    #
    @3
    cF
    crn
    #
    @4
    @8
    cF
    cS
    imassrn
    @3
    cX
    @8
    cF
    wfo
    #
    @12
    @8
    wceq
    @3
    vx
    @7
    cG
    cH
    cF
    cX
    cvv
    ctgp
    cH
    cG
    @7
    cqus
    co
    wceq
    @3
    qustgp.h
    a1i
    #
    cX
    cG
    cbs
    cfv
    wceq
    @3
    qustgpopn.x
    a1i
    #
    qustgpopn.f
    @7
    cvv
    wcel
    #
    @3
    cG
    cY
    cqg
    ovex
    #
    a1i
    #
    @0
    @1
    @2
    simp1
    #
    quslem
    #
    cX
    @8
    cF
    forn
    syl
    syl5sseq
    @3
    @11
    vy
    cv
    #
    vu
    cv
    #
    wcel
    #
    @22
    @10
    wss
    #
    wa
    #
    vu
    cJ
    wrex
    #
    vy
    @10
    wral
    #
    @3
    @26
    vy
    @10
    @21
    @10
    wcel
    @21
    cX
    wcel
    #
    @21
    @7
    cec
    #
    @4
    wcel
    #
    wa
    @3
    @26
    @30
    vy
    @10
    cX
    vy
    cX
    @29
    @4
    cF
    cF
    vx
    cX
    vx
    cv
    #
    @7
    cec
    #
    cmpt
    #
    vy
    cX
    @29
    cmpt
    qustgpopn.f
    vx
    vy
    cX
    @32
    @29
    @31
    @21
    @7
    eceq1
    cbvmptv
    eqtri
    mptpreima
    rabeq2i
    @3
    @28
    @30
    @26
    @30
    vz
    cv
    #
    cF
    cfv
    #
    @29
    wceq
    #
    vz
    cS
    wrex
    #
    @3
    @28
    wa
    #
    @26
    cF
    wfun
    @30
    @37
    vx
    cX
    @32
    cF
    qustgpopn.f
    funmpt2
    vz
    @29
    cS
    cF
    fvelima
    mpan
    @38
    @36
    @26
    vz
    cS
    @38
    @34
    cS
    wcel
    #
    wa
    #
    @36
    @28
    @34
    cX
    wcel
    #
    @21
    cG
    cminusg
    cfv
    #
    cfv
    #
    @34
    cG
    cplusg
    cfv
    #
    co
    #
    cY
    wcel
    #
    w3a
    #
    @26
    @40
    @36
    @29
    @34
    @7
    cec
    #
    wceq
    #
    @21
    @34
    @7
    wbr
    #
    @47
    @40
    @36
    @48
    @29
    wceq
    @49
    @40
    @35
    @48
    @29
    @40
    @41
    @35
    @48
    wceq
    @38
    cS
    cX
    @34
    @3
    cS
    cX
    wss
    #
    @28
    @3
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @2
    @51
    @3
    @0
    @52
    @19
    cG
    cJ
    cX
    qustgpopn.j
    qustgpopn.x
    tgptopon
    syl
    #
    @0
    @1
    @2
    simp3
    #
    cS
    cJ
    cX
    toponss
    syl2anc
    adantr
    #
    sselda
    #
    vx
    @34
    @32
    @48
    cX
    cF
    @31
    @34
    @7
    eceq1
    qustgpopn.f
    @16
    @48
    cvv
    wcel
    @17
    @34
    cvv
    @7
    ecexg
    ax-mp
    fvmpt
    syl
    eqeq1d
    @48
    @29
    eqcom
    syl6bb
    @40
    @21
    @34
    @7
    cX
    @40
    cY
    cG
    csubg
    cfv
    wcel
    #
    cX
    @7
    wer
    #
    @3
    @57
    @28
    @39
    @1
    @0
    @57
    @2
    cY
    cG
    nsgsubg
    3ad2ant2
    ad2antrr
    #
    @7
    cG
    cX
    cY
    qustgpopn.x
    @7
    eqid
    #
    eqger
    syl
    #
    @3
    @28
    @39
    simplr
    #
    erth
    @40
    @0
    cY
    cX
    wss
    #
    @50
    @47
    wb
    @3
    @0
    @28
    @39
    @19
    ad2antrr
    #
    @40
    @57
    @63
    @59
    cX
    cY
    cG
    qustgpopn.x
    subgss
    syl
    #
    @21
    @34
    @44
    @7
    cY
    cG
    @42
    ctgp
    cX
    qustgpopn.x
    @42
    eqid
    #
    @44
    eqid
    #
    @60
    eqgval
    syl2anc
    3bitr2d
    @40
    @47
    @26
    @40
    @28
    @46
    @26
    @41
    @40
    @46
    wa
    #
    va
    cX
    va
    cv
    #
    @45
    @44
    co
    #
    cmpt
    #
    ccnv
    cS
    cima
    #
    cJ
    wcel
    #
    @21
    @72
    wcel
    #
    @72
    @10
    wss
    #
    @26
    @68
    @71
    cJ
    cJ
    ccn
    co
    wcel
    #
    @2
    @73
    @68
    @71
    cJ
    cJ
    chmeo
    co
    #
    wcel
    @76
    @68
    @71
    va
    cX
    @45
    @69
    cG
    coppg
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cmpt
    #
    @77
    va
    cX
    @80
    @70
    @44
    @79
    cG
    @78
    @45
    @69
    @67
    @78
    eqid
    #
    @79
    eqid
    #
    oppgplus
    mpteq2i
    @68
    @78
    ctgp
    wcel
    #
    @45
    cX
    wcel
    #
    @81
    @77
    wcel
    @68
    @0
    @84
    @40
    @0
    @46
    @64
    adantr
    #
    cG
    @78
    @82
    oppgtgp
    syl
    @40
    cY
    cX
    @45
    @65
    sselda
    #
    va
    @45
    @79
    @81
    @78
    cJ
    cX
    @81
    eqid
    cX
    cG
    @78
    @82
    qustgpopn.x
    oppgbas
    @83
    cG
    cJ
    @78
    @82
    qustgpopn.j
    oppgtopn
    tgplacthmeo
    syl2anc
    syl5eqelr
    @71
    cJ
    cJ
    hmeocn
    syl
    @3
    @2
    @28
    @39
    @46
    @54
    ad3antrrr
    cS
    @71
    cJ
    cJ
    cnima
    syl2anc
    @68
    @28
    @21
    @45
    @44
    co
    #
    cS
    wcel
    #
    @74
    @40
    @28
    @46
    @62
    adantr
    #
    @68
    @88
    @34
    cS
    @68
    @21
    @43
    @44
    co
    #
    @34
    @44
    co
    #
    cG
    c0g
    cfv
    #
    @34
    @44
    co
    #
    @88
    @34
    @68
    @91
    @93
    @34
    @44
    @68
    cG
    cgrp
    wcel
    #
    @28
    @91
    @93
    wceq
    @68
    @0
    @95
    @86
    cG
    tgpgrp
    syl
    #
    @90
    cX
    @44
    cG
    @42
    @21
    @93
    qustgpopn.x
    @67
    @93
    eqid
    #
    @66
    grprinv
    syl2anc
    oveq1d
    @68
    @95
    @28
    @43
    cX
    wcel
    #
    @41
    @92
    @88
    wceq
    @96
    @90
    @68
    @95
    @28
    @98
    @96
    @90
    cX
    cG
    @42
    @21
    qustgpopn.x
    @66
    grpinvcl
    syl2anc
    @40
    @41
    @46
    @56
    adantr
    #
    cX
    @44
    cG
    @21
    @43
    @34
    qustgpopn.x
    @67
    grpass
    syl13anc
    @68
    @95
    @41
    @94
    @34
    wceq
    @96
    @99
    cX
    @44
    cG
    @34
    @93
    qustgpopn.x
    @67
    @97
    grplid
    syl2anc
    3eqtr3d
    @38
    @39
    @46
    simplr
    eqeltrd
    @70
    cS
    wcel
    #
    @89
    va
    @21
    cX
    @72
    @69
    @21
    wceq
    @70
    @88
    cS
    @69
    @21
    @45
    @44
    oveq1
    eleq1d
    va
    cX
    @70
    cS
    @71
    @71
    eqid
    mptpreima
    #
    elrab2
    sylanbrc
    @68
    @100
    va
    cX
    crab
    @69
    @7
    cec
    #
    @4
    wcel
    #
    va
    cX
    crab
    @72
    @10
    @68
    @100
    @103
    va
    cX
    @68
    @69
    cX
    wcel
    #
    wa
    #
    @100
    @70
    cF
    cfv
    #
    @4
    wcel
    #
    @103
    @105
    cF
    cX
    wfn
    #
    @51
    @100
    @107
    wi
    vx
    cX
    @32
    cF
    @16
    @32
    cvv
    wcel
    @17
    @31
    cvv
    @7
    ecexg
    ax-mp
    #
    qustgpopn.f
    fnmpti
    @38
    @51
    @39
    @46
    @104
    @55
    ad3antrrr
    @108
    @51
    @100
    @107
    cX
    cS
    cF
    @70
    fnfvima
    3expia
    sylancr
    @105
    @106
    @102
    @4
    @105
    @106
    @70
    @7
    cec
    #
    @102
    @105
    @70
    cX
    wcel
    #
    @106
    @110
    wceq
    @105
    @95
    @104
    @85
    @111
    @68
    @95
    @104
    @96
    adantr
    #
    @68
    @104
    simpr
    #
    @68
    @85
    @104
    @87
    adantr
    #
    cX
    @44
    cG
    @69
    @45
    qustgpopn.x
    @67
    grpcl
    syl3anc
    #
    vx
    @70
    @32
    @110
    cX
    cF
    @31
    @70
    @7
    eceq1
    qustgpopn.f
    @109
    fvmpt3i
    syl
    @105
    @69
    @70
    @7
    cX
    @40
    @58
    @46
    @104
    @61
    ad2antrr
    @105
    @69
    @70
    @7
    wbr
    #
    @104
    @111
    @69
    @42
    cfv
    #
    @70
    @44
    co
    #
    cY
    wcel
    #
    @113
    @115
    @105
    @118
    @45
    cY
    @105
    @117
    @69
    @44
    co
    #
    @45
    @44
    co
    #
    @93
    @45
    @44
    co
    #
    @118
    @45
    @105
    @120
    @93
    @45
    @44
    @105
    @95
    @104
    @120
    @93
    wceq
    @112
    @113
    cX
    @44
    cG
    @42
    @69
    @93
    qustgpopn.x
    @67
    @97
    @66
    grplinv
    syl2anc
    oveq1d
    @105
    @95
    @117
    cX
    wcel
    #
    @104
    @85
    @121
    @118
    wceq
    @112
    @105
    @95
    @104
    @123
    @112
    @113
    cX
    cG
    @42
    @69
    qustgpopn.x
    @66
    grpinvcl
    syl2anc
    @113
    @114
    cX
    @44
    cG
    @117
    @69
    @45
    qustgpopn.x
    @67
    grpass
    syl13anc
    @105
    @95
    @85
    @122
    @45
    wceq
    @112
    @114
    cX
    @44
    cG
    @45
    @93
    qustgpopn.x
    @67
    @97
    grplid
    syl2anc
    3eqtr3d
    @40
    @46
    @104
    simplr
    eqeltrd
    @105
    @95
    @63
    @116
    @104
    @111
    @119
    w3a
    wb
    @112
    @40
    @63
    @46
    @104
    @65
    ad2antrr
    @69
    @70
    @44
    @7
    cY
    cG
    @42
    cgrp
    cX
    qustgpopn.x
    @66
    @67
    @60
    eqgval
    syl2anc
    mpbir3and
    erthi
    eqtr4d
    eleq1d
    sylibd
    ss2rabdv
    @101
    va
    cX
    @102
    @4
    cF
    cF
    @33
    va
    cX
    @102
    cmpt
    qustgpopn.f
    vx
    va
    cX
    @32
    @102
    @31
    @69
    @7
    eceq1
    cbvmptv
    eqtri
    mptpreima
    3sstr4g
    @25
    @74
    @75
    wa
    vu
    @72
    cJ
    @22
    @72
    wceq
    @23
    @74
    @24
    @75
    @22
    @72
    @21
    eleq2
    @22
    @72
    @10
    sseq1
    anbi12d
    rspcev
    syl12anc
    3ad2antr3
    ex
    sylbid
    rexlimdva
    syl5
    expimpd
    syl5bi
    ralrimiv
    @3
    @52
    cJ
    ctop
    wcel
    @11
    @27
    wb
    @53
    cX
    cJ
    topontop
    vy
    vu
    @10
    cJ
    eltop2
    3syl
    mpbird
    @3
    @52
    @13
    @6
    @9
    @11
    wa
    wb
    @53
    @20
    @4
    cF
    cJ
    cX
    @8
    elqtop3
    syl2anc
    mpbir2and
    @3
    @8
    cG
    cH
    cF
    cJ
    cK
    cX
    ctgp
    @3
    vx
    @7
    cG
    cH
    cF
    cX
    cvv
    ctgp
    @14
    @15
    qustgpopn.f
    @18
    @19
    qusval
    @15
    @20
    @19
    qustgpopn.j
    qustgpopn.k
    imastopn
    eleqtrrd
end
