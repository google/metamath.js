include "cres.mm"
include "wf1o.mm"
include "wtru.mm"
include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "csu.mm"
include "wceq.mm"
include "cin.mm"
include "crab.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cmap.mm"
include "wi.mm"
include "weq.mm"
include "wcel.mm"
include "wa.mm"
include "simpl.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "sumeq2dv.mm"
include "eqeq1d.mm"
include "cbvrabv.mm"
include "a1i.mm"
include "reseq2d.mm"
include "eqidd.mm"
include "f1oeq123d.mm"
include "imbi2d.mm"
include "cbits.mm"
include "ccom.mm"
include "cima.mm"
include "cind.mm"
include "eulerpartgbij.mm"
include "w3a.mm"
include "fveq2.mm"
include "reseq1.mm"
include "coeq2d.mm"
include "fveq2d.mm"
include "imaeq2d.mm"
include "eqeq12d.mm"
include "eulerpartlemgv.mm"
include "vtoclga.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "eqtr4d.mm"
include "sumeq2sdv.mm"
include "eulerpartlemgs2.mm"
include "cn0.mm"
include "wss.mm"
include "cvv.mm"
include "nn0ex.mm"
include "0nn0.mm"
include "1nn0.mm"
include "prssi.mm"
include "mp2an.mm"
include "mapss.mm"
include "ssrin.mm"
include "ax-mp.mm"
include "wf.mm"
include "f1of.mm"
include "ffvelrni.mm"
include "sseldi.mm"
include "eulerpartlemsv1.mm"
include "syl.mm"
include "ccnv.mm"
include "cfn.mm"
include "eulerpartlemt0.mm"
include "simp1bi.mm"
include "inss2.mm"
include "sseli.mm"
include "elind.mm"
include "3eqtr3d.mm"
include "eqtr3d.mm"
include "f1oresrab.mm"
include "chvarv.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "raleqdv.mm"
include "nfrab1.mm"
include "df-3an.mm"
include "anbi1i.mm"
include "eulerpartleme.mm"
include "an32.mm"
include "3bitr4i.mm"
include "nnex.mm"
include "elmap.mm"
include "3anbi1i.mm"
include "bitri.mm"
include "wb.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "dfss3.mm"
include "sylib.mm"
include "biantrurd.mm"
include "breq2.mm"
include "notbid.mm"
include "elrab2.mm"
include "ralbii.mm"
include "r19.26.mm"
include "3bitri.mm"
include "syl6rbbr.mm"
include "adantr.mm"
include "pm5.32i.mm"
include "bitr4i.mm"
include "rabid.mm"
include "eqri.mm"
include "3eqtri.mm"
include "reseq2i.mm"
include "nfcv.mm"
include "wfn.mm"
include "crn.mm"
include "fnima.mm"
include "sseq1d.mm"
include "anbi2d.mm"
include "sstr.mm"
include "mpan2.mm"
include "pm4.71ri.mm"
include "syl6bbr.mm"
include "anass.mm"
include "df-f.mm"
include "3bitr4ri.mm"
include "prex.mm"
include "vex.mm"
include "eleq1d.mm"
include "elab2.mm"
include "anbi12i.mm"
include "elin.mm"
include "eulerpartlemd.mm"
include "mpbird.mm"
include "trud.mm"

theorem eulerpartlemn
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let vo: setvar o
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cM: class M
  let cN: class N
  let cO: class O
  let vr: setvar r
  let vd: setvar d
  let vq: setvar q
  assume eulerpart.p: |- P = { f e. ( NN0 ^m NN ) | ( ( `' f " NN ) e. Fin /\ sum_ k e. NN ( ( f ` k ) x. k ) = N ) }
  assume eulerpart.o: |- O = { g e. P | A. n e. ( `' g " NN ) -. 2 || n }
  assume eulerpart.d: |- D = { g e. P | A. n e. NN ( g ` n ) <_ 1 }
  assume eulerpart.j: |- J = { z e. NN | -. 2 || z }
  assume eulerpart.f: |- F = ( x e. J , y e. NN0 |-> ( ( 2 ^ y ) x. x ) )
  assume eulerpart.h: |- H = { r e. ( ( ~P NN0 i^i Fin ) ^m J ) | ( r supp (/) ) e. Fin }
  assume eulerpart.m: |- M = ( r e. H |-> { <. x , y >. | ( x e. J /\ y e. ( r ` x ) ) } )
  assume eulerpart.r: |- R = { f | ( `' f " NN ) e. Fin }
  assume eulerpart.t: |- T = { f e. ( NN0 ^m NN ) | ( `' f " NN ) C_ J }
  assume eulerpart.g: |- G = ( o e. ( T i^i R ) |-> ( ( _Ind ` NN ) ` ( F " ( M ` ( bits o. ( o |` J ) ) ) ) ) )
  assume eulerpart.s: |- S = ( f e. ( ( NN0 ^m NN ) i^i R ) |-> sum_ k e. NN ( ( f ` k ) x. k ) )

  disjoint f g
  disjoint f k
  disjoint f n
  disjoint f o
  disjoint f r
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g k
  disjoint g n
  disjoint g o
  disjoint g r
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint k n
  disjoint k o
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint n o
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint o r
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F k
  disjoint F n
  disjoint F o
  disjoint F x
  disjoint F y
  disjoint G f
  disjoint G k
  disjoint G o
  disjoint H o
  disjoint H r
  disjoint J f
  disjoint J k
  disjoint J n
  disjoint J o
  disjoint J r
  disjoint J x
  disjoint J y
  disjoint M k
  disjoint M n
  disjoint M o
  disjoint M r
  disjoint M x
  disjoint M y
  disjoint N f
  disjoint N g
  disjoint N k
  disjoint N n
  disjoint N o
  disjoint N x
  disjoint O n
  disjoint O r
  disjoint O x
  disjoint O y
  disjoint P g
  disjoint P k
  disjoint P n
  disjoint R f
  disjoint R k
  disjoint R n
  disjoint R o
  disjoint R r
  disjoint R x
  disjoint R y
  disjoint T f
  disjoint T k
  disjoint T n
  disjoint T o
  disjoint T r
  disjoint T x
  disjoint T y
  disjoint d f
  disjoint d g
  disjoint d k
  disjoint d n
  disjoint d o
  disjoint d q
  disjoint d r
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint f q
  disjoint g q
  disjoint k q
  disjoint n q
  disjoint o q
  disjoint q r
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint D d
  disjoint F d
  disjoint F q
  disjoint G q
  disjoint H q
  disjoint J d
  disjoint J q
  disjoint M d
  disjoint M q
  disjoint N d
  disjoint N q
  disjoint P q
  disjoint R d
  disjoint R q
  disjoint S q
  disjoint T d
  disjoint T q
  assert |- ( G |` O ) : O -1-1-onto-> D

  proof
    cO
    cD
    cG
    cO
    cres
    #
    wf1o
    #
    wtru
    @1
    cn
    vk
    cv
    #
    vq
    cv
    #
    cfv
    #
    @2
    cmul
    co
    #
    vk
    csu
    #
    cN
    wceq
    #
    vq
    cT
    cR
    cin
    #
    crab
    #
    cn
    @2
    vd
    cv
    #
    cfv
    #
    @2
    cmul
    co
    #
    vk
    csu
    #
    cN
    wceq
    #
    vd
    cc0
    c1
    cpr
    #
    cn
    cmap
    co
    #
    cR
    cin
    #
    crab
    #
    cG
    @9
    cres
    #
    wf1o
    #
    wtru
    cn
    @2
    vo
    cv
    #
    cfv
    #
    @2
    cmul
    co
    #
    vk
    csu
    #
    cN
    wceq
    #
    vo
    @8
    crab
    #
    @18
    cG
    @26
    cres
    #
    wf1o
    #
    wi
    wtru
    @20
    wi
    vo
    vq
    vo
    vq
    weq
    #
    @28
    @20
    wtru
    @29
    @26
    @9
    @18
    @18
    @27
    @19
    @29
    @26
    @9
    cG
    @26
    @9
    wceq
    @29
    @25
    @7
    vo
    vq
    @8
    @29
    @24
    @6
    cN
    @29
    cn
    @23
    @5
    vk
    @29
    @2
    cn
    wcel
    #
    wa
    #
    @22
    @4
    @2
    cmul
    @31
    @2
    @21
    @3
    @29
    @30
    simpl
    fveq1d
    oveq1d
    sumeq2dv
    eqeq1d
    cbvrabv
    a1i
    #
    reseq2d
    @32
    @29
    @18
    eqidd
    f1oeq123d
    imbi2d
    wtru
    @25
    @14
    vo
    vd
    @8
    @17
    cF
    cbits
    @21
    cJ
    cres
    #
    ccom
    #
    cM
    cfv
    #
    cima
    #
    cn
    cind
    cfv
    #
    cfv
    #
    cG
    eulerpart.g
    @8
    @17
    cG
    wf1o
    #
    wtru
    vx
    vy
    vz
    cD
    cP
    cR
    cT
    vf
    vg
    vk
    vn
    vo
    cF
    cG
    cH
    cJ
    cM
    cN
    cO
    vr
    eulerpart.p
    eulerpart.o
    eulerpart.d
    eulerpart.j
    eulerpart.f
    eulerpart.h
    eulerpart.m
    eulerpart.r
    eulerpart.t
    eulerpart.g
    eulerpartgbij
    #
    a1i
    wtru
    @21
    @8
    wcel
    #
    @10
    @38
    wceq
    #
    w3a
    #
    @13
    @24
    cN
    @43
    cn
    @2
    @21
    cG
    cfv
    #
    cfv
    #
    @2
    cmul
    co
    #
    vk
    csu
    #
    @13
    @24
    @43
    cn
    @46
    @12
    vk
    @43
    @45
    @11
    @2
    cmul
    @43
    @2
    @44
    @10
    @43
    @44
    @38
    @10
    @41
    wtru
    @44
    @38
    wceq
    #
    @42
    @3
    cG
    cfv
    #
    cF
    cbits
    @3
    cJ
    cres
    #
    ccom
    #
    cM
    cfv
    #
    cima
    #
    @37
    cfv
    #
    wceq
    @48
    vq
    @21
    @8
    vq
    vo
    weq
    #
    @49
    @44
    @54
    @38
    @3
    @21
    cG
    fveq2
    #
    @55
    @53
    @36
    @37
    @55
    @52
    @35
    cF
    @55
    @51
    @34
    cM
    @55
    @50
    @33
    cbits
    @3
    @21
    cJ
    reseq1
    coeq2d
    fveq2d
    imaeq2d
    fveq2d
    eqeq12d
    vx
    vy
    vz
    @3
    cD
    cP
    cR
    cT
    vf
    vg
    vk
    vn
    vo
    cF
    cG
    cH
    cJ
    cM
    cN
    cO
    vr
    eulerpart.p
    eulerpart.o
    eulerpart.d
    eulerpart.j
    eulerpart.f
    eulerpart.h
    eulerpart.m
    eulerpart.r
    eulerpart.t
    eulerpart.g
    eulerpartlemgv
    vtoclga
    3ad2ant2
    wtru
    @41
    @42
    simp3
    eqtr4d
    fveq1d
    oveq1d
    sumeq2sdv
    @41
    wtru
    @47
    @24
    wceq
    @42
    @41
    @44
    cS
    cfv
    #
    @21
    cS
    cfv
    #
    @47
    @24
    @49
    cS
    cfv
    #
    @3
    cS
    cfv
    #
    wceq
    @57
    @58
    wceq
    vq
    @21
    @8
    @55
    @59
    @57
    @60
    @58
    @55
    @49
    @44
    cS
    @56
    fveq2d
    @3
    @21
    cS
    fveq2
    eqeq12d
    vx
    vy
    vz
    @3
    cD
    cP
    cR
    cS
    cT
    vf
    vg
    vk
    vn
    vo
    cF
    cG
    cH
    cJ
    cM
    cN
    cO
    vr
    eulerpart.p
    eulerpart.o
    eulerpart.d
    eulerpart.j
    eulerpart.f
    eulerpart.h
    eulerpart.m
    eulerpart.r
    eulerpart.t
    eulerpart.g
    eulerpart.s
    eulerpartlemgs2
    vtoclga
    @41
    @44
    cn0
    cn
    cmap
    co
    #
    cR
    cin
    #
    wcel
    @57
    @47
    wceq
    @41
    @17
    @62
    @44
    @16
    @61
    wss
    #
    @17
    @62
    wss
    cn0
    cvv
    wcel
    @15
    cn0
    wss
    #
    @63
    nn0ex
    cc0
    cn0
    wcel
    c1
    cn0
    wcel
    @64
    0nn0
    1nn0
    cc0
    c1
    cn0
    prssi
    mp2an
    #
    @15
    cn0
    cn
    cvv
    mapss
    mp2an
    @16
    @61
    cR
    ssrin
    ax-mp
    @8
    @17
    @21
    cG
    @39
    @8
    @17
    cG
    wf
    @40
    @8
    @17
    cG
    f1of
    ax-mp
    ffvelrni
    sseldi
    @44
    cR
    cS
    vf
    vk
    eulerpart.r
    eulerpart.s
    eulerpartlemsv1
    syl
    @41
    @21
    @62
    wcel
    @58
    @24
    wceq
    @41
    @61
    cR
    @21
    @41
    @21
    @61
    wcel
    @21
    ccnv
    cn
    cima
    #
    cfn
    wcel
    @66
    cJ
    wss
    vx
    vy
    vz
    @21
    cD
    cP
    cR
    cT
    vf
    vg
    vk
    vn
    cF
    cH
    cJ
    cM
    cN
    cO
    vr
    eulerpart.p
    eulerpart.o
    eulerpart.d
    eulerpart.j
    eulerpart.f
    eulerpart.h
    eulerpart.m
    eulerpart.r
    eulerpart.t
    eulerpartlemt0
    simp1bi
    @8
    cR
    @21
    cT
    cR
    inss2
    sseli
    elind
    @21
    cR
    cS
    vf
    vk
    eulerpart.r
    eulerpart.s
    eulerpartlemsv1
    syl
    3eqtr3d
    3ad2ant2
    eqtr3d
    eqeq1d
    f1oresrab
    chvarv
    wtru
    cO
    @9
    cD
    @18
    @0
    @19
    @0
    @19
    wceq
    wtru
    cO
    @9
    cG
    cO
    c2
    vn
    cv
    #
    cdvds
    wbr
    #
    wn
    #
    vn
    vg
    cv
    #
    ccnv
    #
    cn
    cima
    #
    wral
    #
    vg
    cP
    crab
    @69
    vn
    @3
    ccnv
    #
    cn
    cima
    #
    wral
    #
    vq
    cP
    crab
    #
    @9
    eulerpart.o
    @73
    @76
    vg
    vq
    cP
    vg
    vq
    weq
    #
    @69
    vn
    @72
    @75
    @78
    @71
    @74
    cn
    @70
    @3
    cnveq
    imaeq1d
    raleqdv
    cbvrabv
    vq
    @77
    @9
    @76
    vq
    cP
    nfrab1
    @7
    vq
    @8
    nfrab1
    @3
    cP
    wcel
    #
    @76
    wa
    #
    @3
    @8
    wcel
    #
    @7
    wa
    #
    @3
    @77
    wcel
    @3
    @9
    wcel
    @80
    cn
    cn0
    @3
    wf
    #
    @75
    cfn
    wcel
    #
    wa
    #
    @76
    wa
    #
    @7
    wa
    #
    @82
    @83
    @84
    @7
    w3a
    #
    @76
    wa
    @85
    @7
    wa
    #
    @76
    wa
    @80
    @87
    @88
    @89
    @76
    @83
    @84
    @7
    df-3an
    anbi1i
    @79
    @88
    @76
    @3
    cP
    vf
    vk
    cN
    eulerpart.p
    eulerpartleme
    anbi1i
    @85
    @76
    @7
    an32
    3bitr4i
    @81
    @86
    @7
    @81
    @83
    @84
    @75
    cJ
    wss
    #
    w3a
    #
    @85
    @90
    wa
    @86
    @81
    @3
    @61
    wcel
    #
    @84
    @90
    w3a
    @91
    vx
    vy
    vz
    @3
    cD
    cP
    cR
    cT
    vf
    vg
    vk
    vn
    cF
    cH
    cJ
    cM
    cN
    cO
    vr
    eulerpart.p
    eulerpart.o
    eulerpart.d
    eulerpart.j
    eulerpart.f
    eulerpart.h
    eulerpart.m
    eulerpart.r
    eulerpart.t
    eulerpartlemt0
    @92
    @83
    @84
    @90
    cn0
    cn
    @3
    nn0ex
    nnex
    elmap
    3anbi1i
    bitri
    @83
    @84
    @90
    df-3an
    @85
    @90
    @76
    @83
    @90
    @76
    wb
    @84
    @83
    @76
    @67
    cn
    wcel
    #
    vn
    @75
    wral
    #
    @76
    wa
    #
    @90
    @83
    @94
    @76
    @83
    @75
    cn
    wss
    @94
    @83
    @3
    cdm
    @75
    cn
    @3
    cn
    cnvimass
    cn
    cn0
    @3
    fdm
    syl5sseq
    vn
    @75
    cn
    dfss3
    sylib
    biantrurd
    @90
    @67
    cJ
    wcel
    #
    vn
    @75
    wral
    @93
    @69
    wa
    #
    vn
    @75
    wral
    @95
    vn
    @75
    cJ
    dfss3
    @96
    @97
    vn
    @75
    c2
    vz
    cv
    #
    cdvds
    wbr
    #
    wn
    @69
    vz
    @67
    cn
    cJ
    vz
    vn
    weq
    @99
    @68
    @98
    @67
    c2
    cdvds
    breq2
    notbid
    eulerpart.j
    elrab2
    ralbii
    @93
    @69
    vn
    @75
    r19.26
    3bitri
    syl6rbbr
    adantr
    pm5.32i
    3bitri
    anbi1i
    bitr4i
    @76
    vq
    cP
    rabid
    @7
    vq
    @8
    rabid
    3bitr4i
    eqri
    3eqtri
    #
    reseq2i
    a1i
    cO
    @9
    wceq
    wtru
    @100
    a1i
    cD
    @18
    wceq
    wtru
    vd
    cD
    @18
    vd
    cD
    nfcv
    @14
    vd
    @17
    nfrab1
    @10
    @17
    wcel
    #
    @14
    wa
    #
    @10
    cP
    wcel
    #
    @10
    cn
    cima
    #
    @15
    wss
    #
    wa
    #
    @10
    @18
    wcel
    @10
    cD
    wcel
    @102
    cn
    cn0
    @10
    wf
    #
    @10
    ccnv
    #
    cn
    cima
    #
    cfn
    wcel
    #
    wa
    #
    @105
    wa
    #
    @14
    wa
    #
    @106
    @101
    @112
    @14
    @10
    @16
    wcel
    #
    @10
    cR
    wcel
    #
    wa
    @107
    @105
    wa
    #
    @110
    wa
    @101
    @112
    @114
    @116
    @115
    @110
    cn
    @15
    @10
    wf
    #
    @10
    cn
    wfn
    #
    @10
    crn
    #
    cn0
    wss
    #
    wa
    #
    @105
    wa
    #
    @114
    @116
    @118
    @120
    @105
    wa
    #
    wa
    @118
    @119
    @15
    wss
    #
    wa
    @122
    @117
    @118
    @123
    @124
    @118
    @123
    @120
    @124
    wa
    @124
    @118
    @105
    @124
    @120
    @118
    @104
    @119
    @15
    cn
    @10
    fnima
    sseq1d
    anbi2d
    @124
    @120
    @124
    @64
    @120
    @65
    @119
    @15
    cn0
    sstr
    mpan2
    pm4.71ri
    syl6bbr
    pm5.32i
    @118
    @120
    @105
    anass
    cn
    @15
    @10
    df-f
    3bitr4ri
    @15
    cn
    @10
    cc0
    c1
    prex
    nnex
    elmap
    @107
    @121
    @105
    cn
    cn0
    @10
    df-f
    anbi1i
    3bitr4i
    vf
    cv
    #
    ccnv
    #
    cn
    cima
    #
    cfn
    wcel
    @110
    vf
    @10
    cR
    vd
    vex
    vf
    vd
    weq
    #
    @127
    @109
    cfn
    @128
    @126
    @108
    cn
    @125
    @10
    cnveq
    imaeq1d
    eleq1d
    eulerpart.r
    elab2
    anbi12i
    @10
    @16
    cR
    elin
    @107
    @110
    @105
    an32
    3bitr4i
    anbi1i
    @106
    @107
    @110
    @14
    w3a
    #
    @105
    wa
    @111
    @14
    wa
    #
    @105
    wa
    @113
    @103
    @129
    @105
    @10
    cP
    vf
    vk
    cN
    eulerpart.p
    eulerpartleme
    anbi1i
    @129
    @130
    @105
    @107
    @110
    @14
    df-3an
    anbi1i
    @111
    @14
    @105
    an32
    3bitri
    bitr4i
    @14
    vd
    @17
    rabid
    @10
    cD
    cP
    vf
    vg
    vk
    vn
    cN
    cO
    eulerpart.p
    eulerpart.o
    eulerpart.d
    eulerpartlemd
    3bitr4ri
    eqri
    a1i
    f1oeq123d
    mpbird
    trud
end
