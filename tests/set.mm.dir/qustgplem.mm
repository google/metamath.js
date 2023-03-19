include "ctgp.mm"
include "wcel.mm"
include "cnsg.mm"
include "cfv.mm"
include "wa.mm"
include "cgrp.mm"
include "ctps.mm"
include "csg.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "qusgrp.mm"
include "adantl.mm"
include "cbs.mm"
include "ctopon.mm"
include "cqg.mm"
include "cqs.mm"
include "cqtop.mm"
include "cvv.mm"
include "cqus.mm"
include "wceq.mm"
include "a1i.mm"
include "ovex.mm"
include "simpl.mm"
include "qusval.mm"
include "quslem.mm"
include "imastopn.mm"
include "wfo.mm"
include "tgptopon.mm"
include "adantr.mm"
include "qtoptopon.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "qusbas.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "eqid.mm"
include "istps.mm"
include "sylibr.mm"
include "cxp.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "grpsubf.mm"
include "syl.mm"
include "wss.mm"
include "wrex.mm"
include "cab.mm"
include "wrel.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "relxp.mm"
include "relss.mm"
include "mpisyl.mm"
include "cop.mm"
include "sseld.mm"
include "cec.mm"
include "wi.mm"
include "vex.mm"
include "elqs.mm"
include "eleq2d.mm"
include "syl5bbr.mm"
include "anbi12d.mm"
include "reeanv.mm"
include "opelxp.mm"
include "3bitr4g.mm"
include "wfn.mm"
include "wb.mm"
include "ad2antrr.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "df-ov.mm"
include "simpllr.mm"
include "simprl.mm"
include "simprr.mm"
include "qussub.mm"
include "syl3anc.mm"
include "syl5eqr.mm"
include "eleq1d.mm"
include "simpr.mm"
include "cmpt2.mm"
include "tgpgrp.mm"
include "fnov.mm"
include "sylib.mm"
include "tgpsubcn.mm"
include "eqeltrrd.mm"
include "cmpt.mm"
include "ecexg.mm"
include "ax-mp.mm"
include "fnmpti.mm"
include "qtopid.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "syl5eqelr.mm"
include "eceq1.mm"
include "cnmpt21.mm"
include "syl5eqel.mm"
include "simplr.mm"
include "cnima.mm"
include "eltx.mm"
include "mpbid.mm"
include "fnmpt2i.mm"
include "anbi1i.mm"
include "weq.mm"
include "oveq12.mm"
include "eceq1d.mm"
include "ovmpt2a.mm"
include "pm5.32i.mm"
include "3bitri.mm"
include "eleq1.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "2rexbidv.mm"
include "rspccv.mm"
include "syl5bir.mm"
include "mpand.mm"
include "simp-4l.mm"
include "simprll.mm"
include "qustgpopn.mm"
include "simprlr.mm"
include "fvmpt3i.mm"
include "toponss.mm"
include "simprrl.mm"
include "simpld.mm"
include "fnfvima.mm"
include "mp3an1.mm"
include "simprd.mm"
include "opelxpi.mm"
include "sselda.mm"
include "anim12dan.mm"
include "opeq12.mm"
include "syl2an.mm"
include "quseccl.mm"
include "3expb.mm"
include "eqtr4d.mm"
include "3eqtr3g.mm"
include "simprrr.mm"
include "sylan2.mm"
include "simprbi.mm"
include "mpbir2and.mm"
include "ralrimivva.mm"
include "opeq1.mm"
include "ralbidv.mm"
include "ralima.mm"
include "mpan.mm"
include "opeq2.mm"
include "sylan9bb.mm"
include "mpbird.mm"
include "dfss3.mm"
include "ralxp.mm"
include "bitri.mm"
include "xpeq1.mm"
include "sseq1d.mm"
include "xpeq2.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "syld.mm"
include "sylbid.mm"
include "adantld.mm"
include "opex.mm"
include "elab.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "sylbird.mm"
include "com23.mm"
include "mpdd.mm"
include "relssdv.mm"
include "ssabral.mm"
include "ralrimiva.mm"
include "txtopon.mm"
include "iscn.mm"
include "istgp2.mm"
include "syl3anbrc.mm"

theorem qustgplem
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let c.mi: class .-
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
  let vy: setvar y
  let cS: class S
  assume qustgp.h: |- H = ( G /s ( G ~QG Y ) )
  assume qustgpopn.x: |- X = ( Base ` G )
  assume qustgpopn.j: |- J = ( TopOpen ` G )
  assume qustgpopn.k: |- K = ( TopOpen ` H )
  assume qustgpopn.f: |- F = ( x e. X |-> [ x ] ( G ~QG Y ) )
  assume qustgplem.m: |- .- = ( z e. X , w e. X |-> [ ( z ( -g ` G ) w ) ] ( G ~QG Y ) )

  disjoint w x
  disjoint w z
  disjoint G w
  disjoint x z
  disjoint G x
  disjoint G z
  disjoint J w
  disjoint J x
  disjoint J z
  disjoint F w
  disjoint F z
  disjoint X w
  disjoint X x
  disjoint X z
  disjoint H w
  disjoint H x
  disjoint H z
  disjoint K w
  disjoint K x
  disjoint K z
  disjoint Y w
  disjoint Y x
  disjoint Y z
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
  disjoint w y
  disjoint x y
  disjoint y z
  disjoint G y
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
  disjoint J y
  disjoint F a
  disjoint F p
  disjoint F q
  disjoint F r
  disjoint F s
  disjoint F u
  disjoint F y
  disjoint S a
  disjoint S u
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X p
  disjoint X q
  disjoint X u
  disjoint X y
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H d
  disjoint H p
  disjoint H q
  disjoint H r
  disjoint H s
  disjoint H u
  disjoint H y
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint K d
  disjoint K p
  disjoint K q
  disjoint K r
  disjoint K s
  disjoint K u
  disjoint K y
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
  disjoint Y y
  assert |- ( ( G e. TopGrp /\ Y e. ( NrmSGrp ` G ) ) -> H e. TopGrp )

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
    wa
    #
    cH
    cgrp
    wcel
    #
    cH
    ctps
    wcel
    #
    cH
    csg
    cfv
    #
    cK
    cK
    ctx
    co
    #
    cK
    ccn
    co
    wcel
    #
    cH
    ctgp
    wcel
    @1
    @3
    @0
    cY
    cG
    cH
    qustgp.h
    qusgrp
    adantl
    #
    @2
    cK
    cH
    cbs
    cfv
    #
    ctopon
    cfv
    #
    wcel
    #
    @4
    @2
    cK
    cX
    cG
    cY
    cqg
    co
    #
    cqs
    #
    ctopon
    cfv
    #
    @10
    @2
    cK
    cJ
    cF
    cqtop
    co
    #
    @14
    @2
    @13
    cG
    cH
    cF
    cJ
    cK
    cX
    ctgp
    @2
    vx
    @12
    cG
    cH
    cF
    cX
    cvv
    ctgp
    cH
    cG
    @12
    cqus
    co
    wceq
    @2
    qustgp.h
    a1i
    #
    cX
    cG
    cbs
    cfv
    wceq
    @2
    qustgpopn.x
    a1i
    #
    qustgpopn.f
    @12
    cvv
    wcel
    #
    @2
    cG
    cY
    cqg
    ovex
    #
    a1i
    #
    @0
    @1
    simpl
    #
    qusval
    @17
    @2
    vx
    @12
    cG
    cH
    cF
    cX
    cvv
    ctgp
    @16
    @17
    qustgpopn.f
    @20
    @21
    quslem
    #
    @21
    qustgpopn.j
    qustgpopn.k
    imastopn
    #
    @2
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cX
    @13
    cF
    wfo
    @15
    @14
    wcel
    @0
    @25
    @1
    cG
    cJ
    cX
    qustgpopn.j
    qustgpopn.x
    tgptopon
    #
    adantr
    #
    @22
    cF
    cJ
    cX
    @13
    qtoptopon
    syl2anc
    eqeltrd
    @2
    @13
    @9
    ctopon
    @2
    @12
    cG
    cH
    cX
    cvv
    ctgp
    @16
    @17
    @20
    @21
    qusbas
    #
    fveq2d
    eleqtrd
    #
    @9
    cK
    cH
    @9
    eqid
    #
    qustgpopn.k
    istps
    sylibr
    @2
    @7
    @9
    @9
    cxp
    #
    @9
    @5
    wf
    #
    @5
    ccnv
    vu
    cv
    #
    cima
    #
    @6
    wcel
    #
    vu
    cK
    wral
    #
    @2
    @3
    @32
    @8
    @9
    cH
    @5
    @30
    @5
    eqid
    #
    grpsubf
    #
    syl
    #
    @2
    @35
    vu
    cK
    @2
    @33
    cK
    wcel
    #
    wa
    #
    @35
    vw
    cv
    #
    vr
    cv
    #
    vs
    cv
    #
    cxp
    #
    wcel
    #
    @45
    @34
    wss
    #
    wa
    #
    vs
    cK
    wrex
    vr
    cK
    wrex
    #
    vw
    @34
    wral
    #
    @41
    @34
    @49
    vw
    cab
    #
    wss
    @50
    @41
    vx
    vy
    @34
    @51
    @41
    @34
    @31
    wss
    @31
    wrel
    @34
    wrel
    @41
    @5
    cdm
    #
    @34
    @31
    @5
    @33
    cnvimass
    @2
    @52
    @31
    wceq
    #
    @40
    @2
    @32
    @53
    @39
    @31
    @9
    @5
    fdm
    syl
    adantr
    syl5sseq
    #
    @9
    @9
    relxp
    @34
    @31
    relss
    mpisyl
    @41
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @34
    wcel
    #
    @57
    @31
    wcel
    #
    @57
    @51
    wcel
    #
    @41
    @34
    @31
    @57
    @54
    sseld
    @41
    @59
    @58
    @60
    @41
    @59
    @55
    va
    cv
    #
    @12
    cec
    #
    wceq
    #
    @56
    vb
    cv
    #
    @12
    cec
    #
    wceq
    #
    wa
    #
    vb
    cX
    wrex
    va
    cX
    wrex
    #
    @58
    @60
    wi
    #
    @41
    @63
    va
    cX
    wrex
    #
    @66
    vb
    cX
    wrex
    #
    wa
    @55
    @9
    wcel
    #
    @56
    @9
    wcel
    #
    wa
    @68
    @59
    @41
    @70
    @72
    @71
    @73
    @70
    @55
    @13
    wcel
    @41
    @72
    va
    cX
    @55
    @12
    vx
    vex
    elqs
    @41
    @13
    @9
    @55
    @2
    @13
    @9
    wceq
    @40
    @28
    adantr
    #
    eleq2d
    syl5bbr
    @71
    @56
    @13
    wcel
    @41
    @73
    vb
    cX
    @56
    @12
    vy
    vex
    elqs
    @41
    @13
    @9
    @56
    @74
    eleq2d
    syl5bbr
    anbi12d
    @63
    @66
    va
    vb
    cX
    cX
    reeanv
    @55
    @56
    @9
    @9
    opelxp
    3bitr4g
    @41
    @67
    @69
    va
    vb
    cX
    cX
    @41
    @61
    cX
    wcel
    #
    @64
    cX
    wcel
    #
    wa
    #
    wa
    #
    @69
    @67
    @62
    @65
    cop
    #
    @34
    wcel
    #
    @79
    @45
    wcel
    #
    @47
    wa
    #
    vs
    cK
    wrex
    vr
    cK
    wrex
    #
    wi
    @78
    @80
    @79
    @31
    wcel
    #
    @79
    @5
    cfv
    #
    @33
    wcel
    #
    wa
    #
    @83
    @78
    @32
    @5
    @31
    wfn
    #
    @80
    @87
    wb
    @78
    @3
    @32
    @2
    @3
    @40
    @77
    @8
    ad2antrr
    @38
    syl
    #
    @31
    @9
    @5
    ffn
    #
    @31
    @79
    @33
    @5
    elpreima
    3syl
    @78
    @86
    @83
    @84
    @78
    @86
    @61
    @64
    cG
    csg
    cfv
    #
    co
    #
    @12
    cec
    #
    @33
    wcel
    #
    @83
    @78
    @85
    @93
    @33
    @78
    @85
    @62
    @65
    @5
    co
    #
    @93
    @62
    @65
    @5
    df-ov
    @78
    @1
    @75
    @76
    @95
    @93
    wceq
    @0
    @1
    @40
    @77
    simpllr
    #
    @41
    @75
    @76
    simprl
    #
    @41
    @75
    @76
    simprr
    #
    cY
    cG
    cH
    @91
    @5
    cX
    @61
    @64
    qustgp.h
    qustgpopn.x
    @91
    eqid
    #
    @37
    qussub
    syl3anc
    syl5eqr
    eleq1d
    @78
    @94
    @61
    vc
    cv
    #
    wcel
    #
    @64
    vd
    cv
    #
    wcel
    #
    wa
    #
    @100
    @102
    cxp
    #
    c.mi
    ccnv
    @33
    cima
    #
    wss
    #
    wa
    #
    vd
    cJ
    wrex
    vc
    cJ
    wrex
    #
    @83
    @78
    @77
    @94
    @109
    @41
    @77
    simpr
    @78
    vt
    cv
    #
    @105
    wcel
    #
    @107
    wa
    #
    vd
    cJ
    wrex
    vc
    cJ
    wrex
    #
    vt
    @106
    wral
    #
    @77
    @94
    wa
    #
    @109
    wi
    @78
    @106
    cJ
    cJ
    ctx
    co
    #
    wcel
    #
    @114
    @78
    c.mi
    @116
    cK
    ccn
    co
    #
    wcel
    #
    @40
    @117
    @2
    @119
    @40
    @77
    @2
    c.mi
    vz
    vw
    cX
    cX
    vz
    cv
    #
    @42
    @91
    co
    #
    @12
    cec
    #
    cmpt2
    @118
    qustgplem.m
    @2
    vz
    vw
    vx
    @121
    @55
    @12
    cec
    #
    @122
    cJ
    cJ
    cJ
    cK
    cX
    cX
    cX
    @27
    @27
    @2
    @91
    vz
    vw
    cX
    cX
    @121
    cmpt2
    #
    @116
    cJ
    ccn
    co
    #
    @2
    @91
    cX
    cX
    cxp
    #
    wfn
    #
    @91
    @124
    wceq
    @2
    cG
    cgrp
    wcel
    #
    @126
    cX
    @91
    wf
    @127
    @0
    @128
    @1
    cG
    tgpgrp
    adantr
    cX
    cG
    @91
    qustgpopn.x
    @99
    grpsubf
    @126
    cX
    @91
    ffn
    3syl
    vz
    vw
    cX
    cX
    @91
    fnov
    sylib
    @0
    @91
    @125
    wcel
    @1
    cG
    cJ
    @91
    qustgpopn.j
    @99
    tgpsubcn
    adantr
    eqeltrrd
    @27
    @2
    vx
    cX
    @123
    cmpt
    cF
    cJ
    cK
    ccn
    co
    #
    qustgpopn.f
    @2
    cF
    cJ
    @15
    ccn
    co
    #
    @129
    @2
    @25
    cF
    cX
    wfn
    #
    cF
    @130
    wcel
    @27
    vx
    cX
    @123
    cF
    @18
    @123
    cvv
    wcel
    @19
    @55
    cvv
    @12
    ecexg
    ax-mp
    #
    qustgpopn.f
    fnmpti
    #
    cF
    cJ
    cX
    qtopid
    sylancl
    @2
    cK
    @15
    cJ
    ccn
    @23
    oveq2d
    eleqtrrd
    syl5eqelr
    @55
    @121
    @12
    eceq1
    cnmpt21
    syl5eqel
    ad2antrr
    @2
    @40
    @77
    simplr
    @33
    c.mi
    @116
    cK
    cnima
    syl2anc
    @78
    @25
    @25
    @117
    @114
    wb
    @2
    @25
    @40
    @77
    @27
    ad2antrr
    #
    @134
    vc
    vd
    @106
    cJ
    cJ
    @24
    @24
    vt
    eltx
    syl2anc
    mpbid
    @115
    @61
    @64
    cop
    #
    @106
    wcel
    #
    @114
    @109
    @136
    @135
    @126
    wcel
    #
    @135
    c.mi
    cfv
    #
    @33
    wcel
    #
    wa
    #
    @77
    @139
    wa
    @115
    c.mi
    @126
    wfn
    #
    @136
    @140
    wb
    vz
    vw
    cX
    cX
    @122
    c.mi
    qustgplem.m
    @18
    @122
    cvv
    wcel
    @19
    @121
    cvv
    @12
    ecexg
    ax-mp
    fnmpt2i
    #
    @126
    @135
    @33
    c.mi
    elpreima
    ax-mp
    @137
    @77
    @139
    @61
    @64
    cX
    cX
    opelxp
    anbi1i
    @77
    @139
    @94
    @77
    @138
    @93
    @33
    @77
    @138
    @61
    @64
    c.mi
    co
    @93
    @61
    @64
    c.mi
    df-ov
    vz
    vw
    @61
    @64
    cX
    cX
    @122
    @93
    c.mi
    vz
    va
    weq
    vw
    vb
    weq
    wa
    @121
    @92
    @12
    @120
    @61
    @42
    @64
    @91
    oveq12
    eceq1d
    qustgplem.m
    @18
    @93
    cvv
    wcel
    @19
    @92
    cvv
    @12
    ecexg
    ax-mp
    ovmpt2a
    syl5eqr
    eleq1d
    pm5.32i
    3bitri
    @113
    @109
    vt
    @135
    @106
    @110
    @135
    wceq
    #
    @112
    @108
    vc
    vd
    cJ
    cJ
    @143
    @111
    @104
    @107
    @143
    @111
    @135
    @105
    wcel
    @104
    @110
    @135
    @105
    eleq1
    @61
    @64
    @100
    @102
    opelxp
    syl6bb
    anbi1d
    2rexbidv
    rspccv
    syl5bir
    syl
    mpand
    @78
    @108
    @83
    vc
    vd
    cJ
    cJ
    @78
    @100
    cJ
    wcel
    #
    @102
    cJ
    wcel
    #
    wa
    #
    @108
    @83
    @78
    @146
    @108
    wa
    #
    wa
    #
    cF
    @100
    cima
    #
    cK
    wcel
    #
    cF
    @102
    cima
    #
    cK
    wcel
    #
    @79
    @149
    @151
    cxp
    #
    wcel
    #
    @153
    @34
    wss
    #
    @83
    @148
    @0
    @1
    @144
    @150
    @0
    @1
    @40
    @77
    @147
    simp-4l
    #
    @78
    @1
    @147
    @96
    adantr
    #
    @78
    @144
    @145
    @108
    simprll
    #
    vx
    @100
    cF
    cG
    cH
    cJ
    cK
    cX
    cY
    qustgp.h
    qustgpopn.x
    qustgpopn.j
    qustgpopn.k
    qustgpopn.f
    qustgpopn
    syl3anc
    @148
    @0
    @1
    @145
    @152
    @156
    @157
    @78
    @144
    @145
    @108
    simprlr
    #
    vx
    @102
    cF
    cG
    cH
    cJ
    cK
    cX
    cY
    qustgp.h
    qustgpopn.x
    qustgpopn.j
    qustgpopn.k
    qustgpopn.f
    qustgpopn
    syl3anc
    @148
    @62
    @149
    wcel
    @65
    @151
    wcel
    @154
    @148
    @61
    cF
    cfv
    #
    @62
    @149
    @148
    @75
    @160
    @62
    wceq
    @78
    @75
    @147
    @97
    adantr
    vx
    @61
    @123
    @62
    cX
    cF
    @55
    @61
    @12
    eceq1
    qustgpopn.f
    @132
    fvmpt3i
    syl
    @148
    @100
    cX
    wss
    #
    @101
    @160
    @149
    wcel
    #
    @148
    @25
    @144
    @161
    @148
    @0
    @25
    @156
    @26
    syl
    #
    @158
    @100
    cJ
    cX
    toponss
    syl2anc
    #
    @148
    @101
    @103
    @78
    @146
    @104
    @107
    simprrl
    #
    simpld
    @131
    @161
    @101
    @162
    @133
    cX
    @100
    cF
    @61
    fnfvima
    mp3an1
    syl2anc
    eqeltrrd
    @148
    @64
    cF
    cfv
    #
    @65
    @151
    @148
    @76
    @166
    @65
    wceq
    @78
    @76
    @147
    @98
    adantr
    vx
    @64
    @123
    @65
    cX
    cF
    @55
    @64
    @12
    eceq1
    qustgpopn.f
    @132
    fvmpt3i
    syl
    @148
    @102
    cX
    wss
    #
    @103
    @166
    @151
    wcel
    #
    @148
    @25
    @145
    @167
    @163
    @159
    @102
    cJ
    cX
    toponss
    syl2anc
    #
    @148
    @101
    @103
    @165
    simprd
    @131
    @167
    @103
    @168
    @133
    cX
    @102
    cF
    @64
    fnfvima
    mp3an1
    syl2anc
    eqeltrrd
    @62
    @65
    @149
    @151
    opelxpi
    syl2anc
    @148
    @120
    @42
    cop
    #
    @34
    wcel
    #
    vw
    @151
    wral
    #
    vz
    @149
    wral
    #
    @155
    @148
    @173
    vp
    cv
    #
    cF
    cfv
    #
    vq
    cv
    #
    cF
    cfv
    #
    cop
    #
    @34
    wcel
    #
    vq
    @102
    wral
    #
    vp
    @100
    wral
    #
    @148
    @179
    vp
    vq
    @100
    @102
    @148
    @174
    @100
    wcel
    #
    @176
    @102
    wcel
    #
    wa
    #
    wa
    #
    @178
    @174
    @12
    cec
    #
    @176
    @12
    cec
    #
    cop
    #
    @34
    @185
    @174
    cX
    wcel
    #
    @176
    cX
    wcel
    #
    wa
    #
    @178
    @188
    wceq
    #
    @148
    @182
    @189
    @183
    @190
    @148
    @100
    cX
    @174
    @164
    sselda
    @148
    @102
    cX
    @176
    @169
    sselda
    anim12dan
    #
    @189
    @175
    @186
    wceq
    @177
    @187
    wceq
    @192
    @190
    vx
    @174
    @123
    @186
    cX
    cF
    @55
    @174
    @12
    eceq1
    qustgpopn.f
    @132
    fvmpt3i
    vx
    @176
    @123
    @187
    cX
    cF
    @55
    @176
    @12
    eceq1
    qustgpopn.f
    @132
    fvmpt3i
    @175
    @177
    @186
    @187
    opeq12
    syl2an
    syl
    @185
    @188
    @34
    wcel
    #
    @188
    @31
    wcel
    #
    @188
    @5
    cfv
    #
    @33
    wcel
    #
    @185
    @186
    @9
    wcel
    #
    @187
    @9
    wcel
    #
    wa
    #
    @195
    @185
    @1
    @191
    @200
    @148
    @1
    @184
    @157
    adantr
    #
    @193
    @1
    @189
    @198
    @190
    @199
    @9
    cY
    cG
    cH
    cX
    @174
    qustgp.h
    qustgpopn.x
    @30
    quseccl
    @9
    cY
    cG
    cH
    cX
    @176
    qustgp.h
    qustgpopn.x
    @30
    quseccl
    anim12dan
    syl2anc
    @186
    @187
    @9
    @9
    opelxpi
    syl
    @185
    @196
    @174
    @176
    cop
    #
    c.mi
    cfv
    #
    @33
    @185
    @186
    @187
    @5
    co
    #
    @174
    @176
    c.mi
    co
    #
    @196
    @203
    @185
    @204
    @174
    @176
    @91
    co
    #
    @12
    cec
    #
    @205
    @185
    @1
    @191
    @204
    @207
    wceq
    #
    @201
    @193
    @1
    @189
    @190
    @208
    cY
    cG
    cH
    @91
    @5
    cX
    @174
    @176
    qustgp.h
    qustgpopn.x
    @99
    @37
    qussub
    3expb
    syl2anc
    @185
    @191
    @205
    @207
    wceq
    @193
    vz
    vw
    @174
    @176
    cX
    cX
    @122
    @207
    c.mi
    vz
    vp
    weq
    vw
    vq
    weq
    wa
    @121
    @206
    @12
    @120
    @174
    @42
    @176
    @91
    oveq12
    eceq1d
    qustgplem.m
    @18
    @207
    cvv
    wcel
    @19
    @206
    cvv
    @12
    ecexg
    ax-mp
    ovmpt2a
    syl
    eqtr4d
    @186
    @187
    @5
    df-ov
    @174
    @176
    c.mi
    df-ov
    3eqtr3g
    @185
    @202
    @106
    wcel
    #
    @203
    @33
    wcel
    #
    @184
    @148
    @202
    @105
    wcel
    @209
    @174
    @176
    @100
    @102
    opelxpi
    @148
    @105
    @106
    @202
    @78
    @146
    @104
    @107
    simprrr
    sselda
    sylan2
    @209
    @202
    @126
    wcel
    #
    @210
    @141
    @209
    @211
    @210
    wa
    wb
    @142
    @126
    @202
    @33
    c.mi
    elpreima
    ax-mp
    simprbi
    syl
    eqeltrd
    @185
    @88
    @194
    @195
    @197
    wa
    wb
    @78
    @88
    @147
    @184
    @78
    @32
    @88
    @89
    @90
    syl
    ad2antrr
    @31
    @188
    @33
    @5
    elpreima
    syl
    mpbir2and
    eqeltrd
    ralrimivva
    @148
    @161
    @167
    @173
    @181
    wb
    @164
    @169
    @161
    @173
    @175
    @42
    cop
    #
    @34
    wcel
    #
    vw
    @151
    wral
    #
    vp
    @100
    wral
    #
    @167
    @181
    @131
    @161
    @173
    @215
    wb
    @133
    @172
    @214
    vz
    vp
    cX
    @100
    cF
    @120
    @175
    wceq
    #
    @171
    @213
    vw
    @151
    @216
    @170
    @212
    @34
    @120
    @175
    @42
    opeq1
    eleq1d
    ralbidv
    ralima
    mpan
    @167
    @214
    @180
    vp
    @100
    @131
    @167
    @214
    @180
    wb
    @133
    @213
    @179
    vw
    vq
    cX
    @102
    cF
    @42
    @177
    wceq
    @212
    @178
    @34
    @42
    @177
    @175
    opeq2
    eleq1d
    ralima
    mpan
    ralbidv
    sylan9bb
    syl2anc
    mpbird
    @155
    @56
    @34
    wcel
    #
    vy
    @153
    wral
    @173
    vy
    @153
    @34
    dfss3
    @217
    @171
    vy
    vz
    vw
    @149
    @151
    @56
    @170
    @34
    eleq1
    ralxp
    bitri
    sylibr
    @82
    @154
    @155
    wa
    @79
    @149
    @44
    cxp
    #
    wcel
    #
    @218
    @34
    wss
    #
    wa
    vr
    vs
    @149
    @151
    cK
    cK
    @43
    @149
    wceq
    #
    @81
    @219
    @47
    @220
    @221
    @45
    @218
    @79
    @43
    @149
    @44
    xpeq1
    #
    eleq2d
    @221
    @45
    @218
    @34
    @222
    sseq1d
    anbi12d
    @44
    @151
    wceq
    #
    @219
    @154
    @220
    @155
    @223
    @218
    @153
    @79
    @44
    @151
    @149
    xpeq2
    #
    eleq2d
    @223
    @218
    @153
    @34
    @224
    sseq1d
    anbi12d
    rspc2ev
    syl112anc
    expr
    rexlimdvva
    syld
    sylbid
    adantld
    sylbid
    @67
    @58
    @80
    @60
    @83
    @67
    @57
    @79
    @34
    @55
    @56
    @62
    @65
    opeq12
    #
    eleq1d
    @67
    @60
    @79
    @51
    wcel
    @83
    @67
    @57
    @79
    @51
    @225
    eleq1d
    @49
    @83
    vw
    @79
    @62
    @65
    opex
    @42
    @79
    wceq
    #
    @48
    @82
    vr
    vs
    cK
    cK
    @226
    @46
    @81
    @47
    @42
    @79
    @45
    eleq1
    anbi1d
    2rexbidv
    elab
    syl6bb
    imbi12d
    syl5ibrcom
    rexlimdvva
    sylbird
    com23
    mpdd
    relssdv
    @49
    vw
    @34
    ssabral
    sylib
    @2
    @35
    @50
    wb
    #
    @40
    @2
    @11
    @11
    @227
    @29
    @29
    vr
    vs
    @34
    cK
    cK
    @10
    @10
    vw
    eltx
    syl2anc
    adantr
    mpbird
    ralrimiva
    @2
    @6
    @31
    ctopon
    cfv
    wcel
    #
    @11
    @7
    @32
    @36
    wa
    wb
    @2
    @11
    @11
    @228
    @29
    @29
    cK
    cK
    @9
    @9
    txtopon
    syl2anc
    @29
    vu
    @5
    @6
    cK
    @31
    @9
    iscn
    syl2anc
    mpbir2and
    cH
    cK
    @5
    qustgpopn.k
    @37
    istgp2
    syl3anbrc
end
