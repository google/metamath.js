include "ccrd.mm"
include "cfv.mm"
include "wbr.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wcel.mm"
include "co.mm"
include "cfn.mm"
include "cvv.mm"
include "wceq.mm"
include "com.mm"
include "csdm.mm"
include "wa.mm"
include "eqid.mm"
include "pm3.2i.mm"
include "cpw.mm"
include "cv.mm"
include "cmap.mm"
include "ciun.mm"
include "wf1.mm"
include "omex.mm"
include "ovex.mm"
include "iunex.mm"
include "f1dmex.mm"
include "sylancl.mm"
include "pwexb.mm"
include "sylibr.mm"
include "pwfseqlem4a.mm"
include "fpwwe2.mm"
include "mpbiri.mm"
include "simprd.mm"
include "wi.mm"
include "wss.mm"
include "cxp.mm"
include "wwe.mm"
include "cin.mm"
include "wsbc.mm"
include "wral.mm"
include "simpld.mm"
include "fpwwe2lem2.mm"
include "mpbid.mm"
include "ssexd.mm"
include "w3a.mm"
include "sseq1.mm"
include "id.mm"
include "sqxpeqd.mm"
include "sseq2d.mm"
include "weeq2.mm"
include "3anbi123d.mm"
include "anbi2d.mm"
include "3expa.mm"
include "adantrr.mm"
include "syl.mm"
include "pm4.71i.mm"
include "syl6bbr.mm"
include "oveq1.mm"
include "eleq12d.mm"
include "breq1.mm"
include "imbi12d.mm"
include "fvex.mm"
include "weeq1.mm"
include "3anbi23d.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "imbi1d.mm"
include "wn.mm"
include "cdom.mm"
include "cdm.mm"
include "wb.mm"
include "con0.mm"
include "omelon.mm"
include "onenon.mm"
include "ax-mp.mm"
include "wex.mm"
include "simpr3.mm"
include "19.8a.mm"
include "ween.mm"
include "domtri2.mm"
include "sylancr.mm"
include "cdif.mm"
include "nfv.mm"
include "nfcv.mm"
include "crab.mm"
include "cint.mm"
include "cif.mm"
include "cmpt2.mm"
include "nfmpt22.mm"
include "nfcxfr.mm"
include "nfov.mm"
include "nfel1.mm"
include "nfim.mm"
include "weq.mm"
include "anbi1d.mm"
include "nfmpt21.mm"
include "xpeq12.mm"
include "anidms.mm"
include "breq2.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "difeq2.mm"
include "pwfseqlem3.mm"
include "chvar.mm"
include "eldifbd.mm"
include "expr.mm"
include "sylbird.mm"
include "con4d.mm"
include "vtocl.mm"
include "vtoclg.mm"
include "mpcom.mm"
include "mpd.mm"
include "isfinite.mm"
include "pwfseqlem2.mm"
include "eqeltrrd.mm"
include "cen.mm"
include "fpwwe2lem3.mm"
include "mpdan.mm"
include "cnvimass.mm"
include "dmss.mm"
include "dmxpss.mm"
include "syl6ss.mm"
include "syl5ss.mm"
include "ssfid.mm"
include "inex1.mm"
include "eqtr3d.mm"
include "wf1o.mm"
include "f1of1.mm"
include "ficardom.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "eqcomd.mm"
include "finnum.mm"
include "carden2.mm"
include "syl2anc.mm"
include "wpss.mm"
include "dfpss2.mm"
include "baib.mm"
include "php3.mm"
include "sdomnen.mm"
include "ex.mm"
include "mt4d.mm"
include "eleqtrrd.mm"
include "eliniseg.mm"
include "sylib.mm"
include "wor.mm"
include "weso.mm"
include "sonr.mm"
include "pm2.65i.mm"

theorem pwfseqlem4
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cD: class D
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  let cZ: class Z
  let vs: setvar s
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let cR: class R
  let cY: class Y
  let cV: class V
  assume pwfseqlem4.g: |- ( ph -> G : ~P A -1-1-> U_ n e. _om ( A ^m n ) )
  assume pwfseqlem4.x: |- ( ph -> X C_ A )
  assume pwfseqlem4.h: |- ( ph -> H : _om -1-1-onto-> X )
  assume pwfseqlem4.ps: |- ( ps <-> ( ( x C_ A /\ r C_ ( x X. x ) /\ r We x ) /\ _om ~<_ x ) )
  assume pwfseqlem4.k: |- ( ( ph /\ ps ) -> K : U_ n e. _om ( x ^m n ) -1-1-> x )
  assume pwfseqlem4.d: |- D = ( G ` { w e. x | ( ( `' K ` w ) e. ran G /\ -. w e. ( `' G ` ( `' K ` w ) ) ) } )
  assume pwfseqlem4.f: |- F = ( x e. _V , r e. _V |-> if ( x e. Fin , ( H ` ( card ` x ) ) , ( D ` |^| { z e. _om | -. ( D ` z ) e. x } ) ) )
  assume pwfseqlem4.w: |- W = { <. a , s >. | ( ( a C_ A /\ s C_ ( a X. a ) ) /\ ( s We a /\ A. b e. a [. ( `' s " { b } ) / v ]. ( v F ( s i^i ( v X. v ) ) ) = b ) ) }
  assume pwfseqlem4.z: |- Z = U. dom W

  disjoint n r
  disjoint n w
  disjoint n x
  disjoint n z
  disjoint r w
  disjoint r x
  disjoint r z
  disjoint w x
  disjoint w z
  disjoint x z
  disjoint D n
  disjoint D z
  disjoint a b
  disjoint a s
  disjoint a v
  disjoint F a
  disjoint b s
  disjoint b v
  disjoint F b
  disjoint s v
  disjoint F s
  disjoint F v
  disjoint G w
  disjoint K w
  disjoint a r
  disjoint a x
  disjoint a z
  disjoint H a
  disjoint b r
  disjoint b x
  disjoint b z
  disjoint H b
  disjoint r s
  disjoint r v
  disjoint H r
  disjoint s x
  disjoint s z
  disjoint H s
  disjoint v x
  disjoint v z
  disjoint H v
  disjoint H x
  disjoint H z
  disjoint a n
  disjoint a ph
  disjoint b n
  disjoint b ph
  disjoint n s
  disjoint n v
  disjoint n ph
  disjoint ph r
  disjoint ph s
  disjoint ph v
  disjoint ph x
  disjoint ph z
  disjoint n ps
  disjoint ps z
  disjoint A a
  disjoint A n
  disjoint A r
  disjoint A s
  disjoint A x
  disjoint A z
  disjoint W a
  disjoint W b
  disjoint W s
  disjoint W v
  disjoint Z a
  disjoint Z b
  disjoint Z s
  disjoint Z v
  disjoint n y
  disjoint y z
  disjoint D y
  disjoint a y
  disjoint b y
  disjoint s y
  disjoint v y
  disjoint F y
  disjoint w y
  disjoint G y
  disjoint K y
  disjoint r y
  disjoint x y
  disjoint H y
  disjoint R s
  disjoint A y
  disjoint Y a
  disjoint Y s
  disjoint V a
  disjoint V r
  disjoint V s
  disjoint V x
  assert |- -. ph

  proof
    wph
    cZ
    ccrd
    cfv
    #
    cH
    cfv
    #
    @1
    cZ
    cW
    cfv
    #
    wbr
    #
    wph
    @1
    @2
    ccnv
    #
    @1
    csn
    #
    cima
    #
    wcel
    #
    @3
    wph
    @1
    cZ
    @6
    wph
    cZ
    @2
    cF
    co
    #
    @1
    cZ
    wph
    cZ
    cfn
    wcel
    #
    @2
    cvv
    wcel
    @8
    @1
    wceq
    wph
    cZ
    com
    csdm
    wbr
    #
    @9
    wph
    @8
    cZ
    wcel
    #
    @10
    wph
    cZ
    @2
    cW
    wbr
    #
    @11
    wph
    @12
    @11
    wa
    cZ
    cZ
    wceq
    #
    @2
    @2
    wceq
    #
    wa
    @13
    @14
    cZ
    eqid
    @2
    eqid
    pm3.2i
    wph
    va
    vb
    vv
    cA
    @2
    cF
    cW
    cZ
    cZ
    vs
    pwfseqlem4.w
    wph
    cA
    cpw
    #
    cvv
    wcel
    #
    cA
    cvv
    wcel
    wph
    @15
    vn
    com
    cA
    vn
    cv
    #
    cmap
    co
    #
    ciun
    #
    cG
    wf1
    @19
    cvv
    wcel
    @16
    pwfseqlem4.g
    vn
    com
    @18
    omex
    cA
    @17
    cmap
    ovex
    iunex
    @15
    @19
    cvv
    cG
    f1dmex
    sylancl
    cA
    pwexb
    sylibr
    #
    wph
    wps
    vx
    vz
    vw
    cA
    cD
    vn
    cF
    cG
    cH
    cK
    cX
    vs
    vr
    va
    pwfseqlem4.g
    pwfseqlem4.x
    pwfseqlem4.h
    pwfseqlem4.ps
    pwfseqlem4.k
    pwfseqlem4.d
    pwfseqlem4.f
    pwfseqlem4a
    pwfseqlem4.z
    fpwwe2
    mpbiri
    #
    simprd
    #
    cZ
    cvv
    wcel
    wph
    @11
    @10
    wi
    #
    wph
    cZ
    cA
    cvv
    @20
    wph
    cZ
    cA
    wss
    #
    @2
    cZ
    cZ
    cxp
    #
    wss
    #
    wph
    @24
    @26
    wa
    #
    cZ
    @2
    wwe
    #
    vv
    cv
    #
    @2
    @29
    @29
    cxp
    cin
    cF
    co
    vb
    cv
    #
    wceq
    vv
    @4
    @30
    csn
    cima
    wsbc
    vb
    cZ
    wral
    #
    wa
    #
    wph
    @12
    @27
    @32
    wa
    #
    wph
    @12
    @11
    @21
    simpld
    #
    wph
    va
    vb
    vv
    cA
    @2
    cF
    cW
    cZ
    vs
    pwfseqlem4.w
    @20
    fpwwe2lem2
    mpbid
    #
    simpld
    #
    simpld
    ssexd
    wph
    va
    cv
    #
    cA
    wss
    #
    @2
    @37
    @37
    cxp
    #
    wss
    #
    @37
    @2
    wwe
    #
    w3a
    #
    wa
    #
    @37
    @2
    cF
    co
    #
    @37
    wcel
    #
    @37
    com
    csdm
    wbr
    #
    wi
    #
    wi
    #
    wph
    @23
    wi
    va
    cZ
    cvv
    @37
    cZ
    wceq
    #
    @43
    wph
    @47
    @23
    @49
    @43
    wph
    @24
    @26
    @28
    w3a
    #
    wa
    wph
    @49
    @42
    @50
    wph
    @49
    @38
    @24
    @40
    @26
    @41
    @28
    @37
    cZ
    cA
    sseq1
    @49
    @39
    @25
    @2
    @49
    @37
    cZ
    @49
    id
    #
    sqxpeqd
    sseq2d
    @37
    cZ
    @2
    weeq2
    3anbi123d
    anbi2d
    wph
    @50
    wph
    @33
    @50
    @35
    @27
    @28
    @50
    @31
    @24
    @26
    @28
    @50
    @50
    id
    3expa
    adantrr
    syl
    pm4.71i
    syl6bbr
    @49
    @45
    @11
    @46
    @10
    @49
    @44
    @8
    @37
    cZ
    @37
    cZ
    @2
    cF
    oveq1
    @51
    eleq12d
    @37
    cZ
    com
    csdm
    breq1
    imbi12d
    imbi12d
    wph
    @38
    vs
    cv
    #
    @39
    wss
    #
    @37
    @52
    wwe
    #
    w3a
    #
    wa
    #
    @37
    @52
    cF
    co
    #
    @37
    wcel
    #
    @46
    wi
    #
    wi
    @48
    vs
    @2
    cZ
    cW
    fvex
    #
    @52
    @2
    wceq
    #
    @56
    @43
    @59
    @47
    @61
    @55
    @42
    wph
    @61
    @53
    @40
    @54
    @41
    @38
    @52
    @2
    @39
    sseq1
    @37
    @52
    @2
    weeq1
    3anbi23d
    anbi2d
    @61
    @58
    @45
    @46
    @61
    @57
    @44
    @37
    @52
    @2
    @37
    cF
    oveq2
    eleq1d
    imbi1d
    imbi12d
    @56
    @46
    @58
    @56
    @46
    wn
    #
    com
    @37
    cdom
    wbr
    #
    @58
    wn
    #
    @56
    com
    ccrd
    cdm
    #
    wcel
    #
    @37
    @65
    wcel
    #
    @63
    @62
    wb
    com
    con0
    wcel
    @66
    omelon
    com
    onenon
    ax-mp
    @56
    @54
    vs
    wex
    #
    @67
    @56
    @54
    @68
    wph
    @38
    @53
    @54
    simpr3
    @54
    vs
    19.8a
    syl
    @37
    vs
    ween
    sylibr
    com
    @37
    domtri2
    sylancr
    wph
    @55
    @63
    @64
    wph
    @55
    @63
    wa
    #
    wa
    #
    @57
    cA
    @37
    wph
    @38
    vr
    cv
    #
    @39
    wss
    #
    @37
    @71
    wwe
    #
    w3a
    #
    @63
    wa
    #
    wa
    #
    @37
    @71
    cF
    co
    #
    cA
    @37
    cdif
    #
    wcel
    #
    wi
    #
    @70
    @57
    @78
    wcel
    #
    wi
    vr
    vs
    @70
    @81
    vr
    @70
    vr
    nfv
    vr
    @57
    @78
    vr
    @37
    @52
    cF
    vr
    @37
    nfcv
    vr
    cF
    vx
    vr
    cvv
    cvv
    vx
    cv
    #
    cfn
    wcel
    @82
    ccrd
    cfv
    cH
    cfv
    vz
    cv
    cD
    cfv
    @82
    wcel
    wn
    vz
    com
    crab
    cint
    cD
    cfv
    cif
    #
    cmpt2
    #
    pwfseqlem4.f
    vx
    vr
    cvv
    cvv
    @83
    nfmpt22
    nfcxfr
    vr
    @52
    nfcv
    nfov
    nfel1
    nfim
    vr
    vs
    weq
    #
    @76
    @70
    @79
    @81
    @85
    @75
    @69
    wph
    @85
    @74
    @55
    @63
    @85
    @72
    @53
    @73
    @54
    @38
    @71
    @52
    @39
    sseq1
    @37
    @71
    @52
    weeq1
    3anbi23d
    anbi1d
    anbi2d
    @85
    @77
    @57
    @78
    @71
    @52
    @37
    cF
    oveq2
    eleq1d
    imbi12d
    wph
    wps
    wa
    #
    @82
    @71
    cF
    co
    #
    cA
    @82
    cdif
    #
    wcel
    #
    wi
    @80
    vx
    va
    @76
    @79
    vx
    @76
    vx
    nfv
    vx
    @77
    @78
    vx
    @37
    @71
    cF
    vx
    @37
    nfcv
    vx
    cF
    @84
    pwfseqlem4.f
    vx
    vr
    cvv
    cvv
    @83
    nfmpt21
    nfcxfr
    vx
    @71
    nfcv
    nfov
    nfel1
    nfim
    vx
    va
    weq
    #
    @86
    @76
    @89
    @79
    @90
    wps
    @75
    wph
    wps
    @82
    cA
    wss
    #
    @71
    @82
    @82
    cxp
    #
    wss
    #
    @82
    @71
    wwe
    #
    w3a
    #
    com
    @82
    cdom
    wbr
    #
    wa
    @90
    @75
    pwfseqlem4.ps
    @90
    @95
    @74
    @96
    @63
    @90
    @91
    @38
    @93
    @72
    @94
    @73
    @82
    @37
    cA
    sseq1
    @90
    @92
    @39
    @71
    @90
    @92
    @39
    wceq
    @82
    @37
    @82
    @37
    xpeq12
    anidms
    sseq2d
    @82
    @37
    @71
    weeq2
    3anbi123d
    @82
    @37
    com
    cdom
    breq2
    anbi12d
    syl5bb
    anbi2d
    @90
    @87
    @77
    @88
    @78
    @82
    @37
    @71
    cF
    oveq1
    @82
    @37
    cA
    difeq2
    eleq12d
    imbi12d
    wph
    wps
    vx
    vz
    vw
    cA
    cD
    vn
    cF
    cG
    cH
    cK
    cX
    vr
    pwfseqlem4.g
    pwfseqlem4.x
    pwfseqlem4.h
    pwfseqlem4.ps
    pwfseqlem4.k
    pwfseqlem4.d
    pwfseqlem4.f
    pwfseqlem3
    chvar
    chvar
    eldifbd
    expr
    sylbird
    con4d
    vtocl
    vtoclg
    mpcom
    mpd
    cZ
    isfinite
    sylibr
    #
    @60
    wph
    wps
    vx
    vz
    vw
    cA
    cD
    @2
    vn
    cF
    cG
    cH
    cK
    cvv
    cX
    cZ
    vr
    pwfseqlem4.g
    pwfseqlem4.x
    pwfseqlem4.h
    pwfseqlem4.ps
    pwfseqlem4.k
    pwfseqlem4.d
    pwfseqlem4.f
    pwfseqlem2
    sylancl
    @22
    eqeltrrd
    #
    wph
    @6
    cZ
    cen
    wbr
    #
    @6
    cZ
    wceq
    #
    wph
    @6
    ccrd
    cfv
    #
    @0
    wceq
    #
    @99
    wph
    @0
    @101
    wph
    @1
    @101
    cH
    cfv
    #
    wceq
    #
    @0
    @101
    wceq
    #
    wph
    @6
    @2
    @6
    @6
    cxp
    #
    cin
    #
    cF
    co
    #
    @1
    @103
    wph
    @1
    cZ
    wcel
    #
    @108
    @1
    wceq
    @98
    wph
    va
    vb
    vv
    cA
    @1
    @2
    cF
    cW
    cZ
    vs
    pwfseqlem4.w
    @20
    @34
    fpwwe2lem3
    mpdan
    wph
    @6
    cfn
    wcel
    #
    @107
    cvv
    wcel
    @108
    @103
    wceq
    wph
    cZ
    @6
    @97
    wph
    @6
    @2
    cdm
    #
    cZ
    @2
    @5
    cnvimass
    wph
    @111
    @25
    cdm
    #
    cZ
    wph
    @26
    @111
    @112
    wss
    wph
    @24
    @26
    @36
    simprd
    @2
    @25
    dmss
    syl
    cZ
    cZ
    dmxpss
    syl6ss
    syl5ss
    #
    ssfid
    #
    @2
    @106
    @60
    inex1
    wph
    wps
    vx
    vz
    vw
    cA
    cD
    @107
    vn
    cF
    cG
    cH
    cK
    cvv
    cX
    @6
    vr
    pwfseqlem4.g
    pwfseqlem4.x
    pwfseqlem4.h
    pwfseqlem4.ps
    pwfseqlem4.k
    pwfseqlem4.d
    pwfseqlem4.f
    pwfseqlem2
    sylancl
    eqtr3d
    wph
    com
    cX
    cH
    wf1
    #
    @0
    com
    wcel
    #
    @101
    com
    wcel
    #
    @104
    @105
    wb
    wph
    com
    cX
    cH
    wf1o
    @115
    pwfseqlem4.h
    com
    cX
    cH
    f1of1
    syl
    wph
    @9
    @116
    @97
    cZ
    ficardom
    syl
    wph
    @110
    @117
    @114
    @6
    ficardom
    syl
    com
    cX
    @0
    @101
    cH
    f1fveq
    syl12anc
    mpbid
    eqcomd
    wph
    @6
    @65
    wcel
    #
    cZ
    @65
    wcel
    #
    @102
    @99
    wb
    wph
    @110
    @118
    @114
    @6
    finnum
    syl
    wph
    @9
    @119
    @97
    cZ
    finnum
    syl
    @6
    cZ
    carden2
    syl2anc
    mpbid
    wph
    @100
    wn
    #
    @6
    cZ
    wpss
    #
    @99
    wn
    #
    wph
    @6
    cZ
    wss
    #
    @121
    @120
    wb
    @113
    @121
    @123
    @120
    @6
    cZ
    dfpss2
    baib
    syl
    wph
    @9
    @121
    @122
    wi
    @97
    @9
    @121
    @122
    @9
    @121
    wa
    @6
    cZ
    csdm
    wbr
    @122
    cZ
    @6
    php3
    @6
    cZ
    sdomnen
    syl
    ex
    syl
    sylbird
    mt4d
    eleqtrrd
    @1
    cvv
    wcel
    @7
    @3
    wb
    @0
    cH
    fvex
    #
    @2
    @1
    @1
    cvv
    @124
    eliniseg
    ax-mp
    sylib
    wph
    cZ
    @2
    wor
    #
    @109
    @3
    wn
    wph
    @28
    @125
    wph
    @28
    @31
    wph
    @27
    @32
    @35
    simprd
    simpld
    cZ
    @2
    weso
    syl
    @98
    cZ
    @1
    @2
    sonr
    syl2anc
    pm2.65i
end
