include "cin.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "wf1o.mm"
include "cind.mm"
include "cfv.mm"
include "cfn.mm"
include "cres.mm"
include "cbits.mm"
include "cv.mm"
include "ccom.mm"
include "cima.mm"
include "cmpt.mm"
include "cpw.mm"
include "ccnv.mm"
include "csn.mm"
include "wcel.mm"
include "crab.mm"
include "cvv.mm"
include "nnex.mm"
include "indf1ofs.mm"
include "ax-mp.mm"
include "wceq.mm"
include "wb.mm"
include "cab.mm"
include "incom.mm"
include "ineq2i.mm"
include "dfrab2.mm"
include "3eqtr4i.mm"
include "wfun.mm"
include "crn.mm"
include "wss.mm"
include "elmapfun.mm"
include "wf.mm"
include "elmapi.mm"
include "frn.mm"
include "syl.mm"
include "wa.mm"
include "fimacnvinrn2.mm"
include "c0.mm"
include "cun.mm"
include "df-pr.mm"
include "indi.mm"
include "wn.mm"
include "0nnn.mm"
include "disjsn.mm"
include "mpbir.mm"
include "1nn.mm"
include "1ex.mm"
include "snss.mm"
include "mpbi.mm"
include "dfss.mm"
include "eqtr2i.mm"
include "uneq12i.mm"
include "3eqtri.mm"
include "uncom.mm"
include "un0.mm"
include "imaeq2i.mm"
include "syl6eq.mm"
include "syl2anc.mm"
include "eleq1d.mm"
include "rabbiia.mm"
include "f1oeq3.mm"
include "cn0.mm"
include "cxp.mm"
include "oddpwdc.mm"
include "f1opwfi.mm"
include "eulerpartlem1.mm"
include "wtru.mm"
include "csupp.mm"
include "bitsf1o.mm"
include "a1i.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "rabex2.mm"
include "nn0ex.mm"
include "pwex.mm"
include "inex1.mm"
include "0nn0.mm"
include "fvres.mm"
include "0bits.mm"
include "cfsupp.mm"
include "frnnn0supp.mm"
include "sylancr.mm"
include "vex.mm"
include "funisfsupp.mm"
include "mp3an23.mm"
include "3eqtr4ri.mm"
include "0ex.mm"
include "bicomd.mm"
include "fcobijfs.mm"
include "elinel1.mm"
include "cores.mm"
include "3syl.mm"
include "mpteq2ia.mm"
include "eqcomi.mm"
include "f1oeq1.mm"
include "mp1i.mm"
include "mpbird.mm"
include "trud.mm"
include "wf1.mm"
include "w3a.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "3pm3.2i.mm"
include "cdif.mm"
include "cnveq.mm"
include "dfn2.mm"
include "imaeq12d.mm"
include "sseq1d.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "eqid.mm"
include "resf1o.mm"
include "mp2an.mm"
include "f1of1.mm"
include "inss1.mm"
include "f1ores.mm"
include "wrex.mm"
include "wfn.mm"
include "resex.mm"
include "fnmpti.mm"
include "fvelimab.mm"
include "elrnmpti.mm"
include "eulerpartlemt.mm"
include "eleq2i.mm"
include "fvtresfn.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "rexbiia.mm"
include "3bitr4ri.mm"
include "bitri.mm"
include "eqriv.mm"
include "resmpt.mm"
include "mp2b.mm"
include "f1oco.mm"
include "wral.mm"
include "f1of.mm"
include "fmpt.mm"
include "biimpri.mm"
include "eqidd.mm"
include "coeq2.mm"
include "fmptcof.mm"
include "eqcomd.mm"
include "f1oeq123d.mm"
include "mpbiri.mm"
include "cz.mm"
include "bitsf.mm"
include "zex.mm"
include "fex.mm"
include "coex.mm"
include "fvmpt2d.mm"
include "ffvelrnda.mm"
include "eqeltrrd.mm"
include "f1ofn.mm"
include "dffn5.mm"
include "fveq2.mm"
include "fmptco.mm"
include "simpr.mm"
include "fvex.mm"
include "fvmpt2.mm"
include "sylancl.mm"
include "imaeq2.mm"
include "cexp.mm"
include "cmul.mm"
include "mpt2exg.mm"
include "imaexg.mm"
include "indf1o.mm"
include "reseq1i.mm"
include "resmpt3.mm"
include "eqtr4i.mm"

theorem eulerpartgbij
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cP: class P
  let cR: class R
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
  let va: setvar a
  let vm: setvar m
  let vb: setvar b
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

  disjoint f g
  disjoint f k
  disjoint f n
  disjoint f o
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g k
  disjoint g n
  disjoint g o
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint k n
  disjoint k o
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint n o
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F o
  disjoint f r
  disjoint J f
  disjoint o r
  disjoint J o
  disjoint r x
  disjoint r y
  disjoint J r
  disjoint J x
  disjoint J y
  disjoint M o
  disjoint M r
  disjoint N f
  disjoint N g
  disjoint N x
  disjoint P g
  disjoint R f
  disjoint R o
  disjoint H o
  disjoint H r
  disjoint T f
  disjoint T o
  disjoint a f
  disjoint a g
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a o
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint f m
  disjoint g m
  disjoint k m
  disjoint m n
  disjoint m o
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint a b
  disjoint F a
  disjoint b o
  disjoint F b
  disjoint a r
  disjoint J a
  disjoint b f
  disjoint b m
  disjoint b r
  disjoint b x
  disjoint b y
  disjoint J b
  disjoint m r
  disjoint J m
  disjoint M a
  disjoint M b
  disjoint R m
  disjoint T m
  assert |- G : ( T i^i R ) -1-1-onto-> ( ( { 0 , 1 } ^m NN ) i^i R )

  proof
    cT
    cR
    cin
    #
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
    cG
    wf1o
    #
    @0
    @3
    cn
    cind
    cfv
    #
    cfn
    cres
    #
    vo
    @0
    cF
    cbits
    vo
    cv
    #
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
    cmpt
    #
    ccom
    #
    wf1o
    #
    cn
    cpw
    #
    cfn
    cin
    #
    @3
    @6
    wf1o
    #
    @0
    @16
    @12
    wf1o
    #
    @14
    @16
    vf
    cv
    #
    ccnv
    #
    c1
    csn
    #
    cima
    #
    cfn
    wcel
    #
    vf
    @2
    crab
    #
    @6
    wf1o
    #
    @17
    cn
    cvv
    wcel
    #
    @25
    nnex
    vf
    cn
    cvv
    indf1ofs
    ax-mp
    @24
    @3
    wceq
    @25
    @17
    wb
    @3
    @20
    cn
    cima
    #
    cfn
    wcel
    #
    vf
    @2
    crab
    #
    @24
    @2
    @28
    vf
    cab
    #
    cin
    @30
    @2
    cin
    @3
    @29
    @2
    @30
    incom
    cR
    @30
    @2
    eulerpart.r
    ineq2i
    @28
    vf
    @2
    dfrab2
    3eqtr4i
    @28
    @23
    vf
    @2
    @19
    @2
    wcel
    #
    @27
    @22
    cfn
    @31
    @19
    wfun
    #
    @19
    crn
    #
    @1
    wss
    #
    @27
    @22
    wceq
    @19
    @1
    cn
    elmapfun
    @31
    cn
    @1
    @19
    wf
    @34
    @19
    @1
    cn
    elmapi
    cn
    @1
    @19
    frn
    syl
    @32
    @34
    wa
    @27
    @20
    cn
    @1
    cin
    #
    cima
    @22
    cn
    @1
    @19
    fimacnvinrn2
    @35
    @21
    @20
    @35
    c0
    @21
    cun
    #
    @21
    c0
    cun
    @21
    @35
    cn
    cc0
    csn
    #
    @21
    cun
    #
    cin
    cn
    @37
    cin
    #
    cn
    @21
    cin
    #
    cun
    @36
    @1
    @38
    cn
    cc0
    c1
    df-pr
    ineq2i
    cn
    @37
    @21
    indi
    @39
    c0
    @40
    @21
    @39
    c0
    wceq
    cc0
    cn
    wcel
    wn
    0nnn
    cn
    cc0
    disjsn
    mpbir
    @21
    @21
    cn
    cin
    #
    @40
    @21
    cn
    wss
    #
    @21
    @41
    wceq
    c1
    cn
    wcel
    @42
    1nn
    c1
    cn
    1ex
    snss
    mpbi
    @21
    cn
    dfss
    mpbi
    @21
    cn
    incom
    eqtr2i
    uneq12i
    3eqtri
    c0
    @21
    uncom
    @21
    un0
    3eqtri
    imaeq2i
    syl6eq
    syl2anc
    eleq1d
    rabbiia
    eqtr2i
    @24
    @3
    @16
    @6
    f1oeq3
    ax-mp
    mpbi
    @0
    @16
    va
    cJ
    cn0
    cxp
    #
    cpw
    cfn
    cin
    #
    cF
    va
    cv
    #
    cima
    #
    cmpt
    #
    vo
    @0
    @10
    cmpt
    #
    ccom
    #
    wf1o
    #
    @18
    @44
    @16
    @47
    wf1o
    #
    @0
    @44
    @48
    wf1o
    #
    @50
    @43
    cn
    cF
    wf1o
    @51
    vx
    vy
    vz
    cF
    cJ
    eulerpart.j
    eulerpart.f
    oddpwdc
    @43
    cn
    cF
    va
    f1opwfi
    ax-mp
    @0
    @44
    cM
    vo
    @0
    @9
    cmpt
    #
    ccom
    #
    wf1o
    #
    @52
    cH
    @44
    cM
    wf1o
    #
    @0
    cH
    @53
    wf1o
    #
    @55
    vx
    vy
    vz
    cD
    cP
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
    eulerpartlem1
    #
    @57
    wtru
    @57
    @0
    vr
    cv
    #
    c0
    csupp
    co
    cfn
    wcel
    #
    vr
    cn0
    cpw
    #
    cfn
    cin
    #
    cJ
    cmap
    co
    #
    crab
    #
    vf
    cn0
    cJ
    cmap
    co
    #
    cR
    cin
    #
    cbits
    @19
    ccom
    #
    cmpt
    #
    vo
    @0
    @8
    cmpt
    #
    ccom
    #
    wf1o
    #
    @66
    @64
    @68
    wf1o
    #
    @0
    @66
    @69
    wf1o
    #
    @71
    @72
    wtru
    @72
    @66
    @64
    vf
    @66
    cbits
    cn0
    cres
    #
    @19
    ccom
    #
    cmpt
    #
    wf1o
    #
    wtru
    c0
    cJ
    cn0
    @62
    cvv
    vf
    vf
    vr
    @74
    cc0
    cvv
    cvv
    @66
    @64
    cn0
    @62
    @74
    wf1o
    wtru
    bitsf1o
    a1i
    cJ
    cvv
    wcel
    #
    wtru
    c2
    vz
    cv
    cdvds
    wbr
    wn
    #
    vz
    cn
    cJ
    eulerpart.j
    nnex
    rabex2
    #
    a1i
    cn0
    cvv
    wcel
    #
    wtru
    nn0ex
    a1i
    @62
    cvv
    wcel
    wtru
    @61
    cfn
    cn0
    nn0ex
    pwex
    inex1
    a1i
    cc0
    cn0
    wcel
    #
    wtru
    0nn0
    a1i
    cc0
    @74
    cfv
    #
    cc0
    cbits
    cfv
    #
    c0
    @82
    @83
    @84
    wceq
    0nn0
    cc0
    cn0
    cbits
    fvres
    ax-mp
    0bits
    eqtr2i
    @19
    cc0
    csupp
    co
    #
    cfn
    wcel
    #
    vf
    @65
    crab
    @28
    vf
    @65
    crab
    #
    @19
    cc0
    cfsupp
    wbr
    #
    vf
    @65
    crab
    @66
    @86
    @28
    vf
    @65
    @19
    @65
    wcel
    #
    @85
    @27
    cfn
    @89
    @78
    cJ
    cn0
    @19
    wf
    #
    @85
    @27
    wceq
    @80
    @19
    cn0
    cJ
    elmapi
    #
    @19
    cJ
    cvv
    frnnn0supp
    sylancr
    eleq1d
    rabbiia
    @88
    @86
    vf
    @65
    @89
    @32
    @88
    @86
    wb
    #
    @19
    cn0
    cJ
    elmapfun
    @32
    @19
    cvv
    wcel
    @82
    @92
    vf
    vex
    0nn0
    @19
    cvv
    cn0
    cc0
    funisfsupp
    mp3an23
    syl
    rabbiia
    @30
    @65
    cin
    @65
    @30
    cin
    @87
    @66
    @30
    @65
    incom
    @28
    vf
    @65
    dfrab2
    cR
    @30
    @65
    eulerpart.r
    ineq2i
    3eqtr4ri
    3eqtr4ri
    @60
    @59
    c0
    cfsupp
    wbr
    #
    vr
    @63
    @59
    @63
    wcel
    @59
    wfun
    #
    @60
    @93
    wb
    @59
    @62
    cJ
    elmapfun
    @94
    @93
    @60
    @94
    @59
    cvv
    wcel
    c0
    cvv
    wcel
    @93
    @60
    wb
    vr
    vex
    0ex
    @59
    cvv
    cvv
    c0
    funisfsupp
    mp3an23
    bicomd
    syl
    rabbiia
    fcobijfs
    @68
    @76
    wceq
    @72
    @77
    wb
    wtru
    @76
    @68
    vf
    @66
    @75
    @67
    @19
    @66
    wcel
    #
    @89
    @75
    @67
    wceq
    #
    @19
    @65
    cR
    elinel1
    @89
    @90
    @33
    cn0
    wss
    @96
    @91
    cJ
    cn0
    @19
    frn
    cbits
    @19
    cn0
    cores
    3syl
    syl
    mpteq2ia
    eqcomi
    @66
    @64
    @68
    @76
    f1oeq1
    mp1i
    mpbird
    trud
    @0
    vo
    cT
    @8
    cmpt
    #
    @0
    cima
    #
    @97
    @0
    cres
    #
    wf1o
    #
    @73
    cT
    @65
    @97
    wf1
    #
    @0
    cT
    wss
    #
    @100
    cT
    @65
    @97
    wf1o
    #
    @101
    @26
    @81
    cJ
    cn
    wss
    #
    w3a
    @82
    @103
    @26
    @81
    @104
    nnex
    nn0ex
    cJ
    @79
    vz
    cn
    crab
    cn
    eulerpart.j
    @79
    vz
    cn
    ssrab2
    eqsstri
    3pm3.2i
    0nn0
    cn
    cn0
    cJ
    vo
    @97
    cvv
    cvv
    cT
    cc0
    cT
    @27
    cJ
    wss
    #
    vf
    cn0
    cn
    cmap
    co
    #
    crab
    @7
    ccnv
    #
    cn0
    @37
    cdif
    #
    cima
    #
    cJ
    wss
    #
    vo
    @106
    crab
    eulerpart.t
    @105
    @110
    vf
    vo
    @106
    @19
    @7
    wceq
    #
    @27
    @109
    cJ
    @111
    @20
    @107
    cn
    @108
    @19
    @7
    cnveq
    cn
    @108
    wceq
    @111
    dfn2
    a1i
    imaeq12d
    sseq1d
    cbvrabv
    eqtri
    @97
    eqid
    #
    resf1o
    mp2an
    cT
    @65
    @97
    f1of1
    ax-mp
    cT
    cR
    inss1
    #
    cT
    @65
    @0
    @97
    f1ores
    mp2an
    @100
    @0
    @66
    @99
    wf1o
    #
    @73
    @98
    @66
    wceq
    @100
    @114
    wb
    vf
    @98
    @66
    @19
    @98
    wcel
    #
    vm
    cv
    #
    @97
    cfv
    #
    @19
    wceq
    #
    vm
    @0
    wrex
    #
    @95
    @97
    cT
    wfn
    @102
    @115
    @119
    wb
    vo
    cT
    @8
    @97
    @7
    cJ
    vo
    vex
    resex
    #
    @112
    fnmpti
    @113
    vm
    cT
    @0
    @19
    @97
    fvelimab
    mp2an
    @19
    vm
    @0
    @116
    cJ
    cres
    #
    cmpt
    #
    crn
    #
    wcel
    @19
    @121
    wceq
    #
    vm
    @0
    wrex
    @95
    @119
    vm
    @0
    @121
    @19
    @122
    @122
    eqid
    @116
    cJ
    vm
    vex
    resex
    elrnmpti
    @66
    @123
    @19
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
    vm
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
    eulerpartlemt
    eleq2i
    @118
    @124
    vm
    @0
    @116
    @0
    wcel
    #
    @118
    @121
    @19
    wceq
    #
    @124
    @125
    @116
    cT
    wcel
    #
    @118
    @126
    wb
    @116
    cT
    cR
    elinel1
    @127
    @117
    @121
    @19
    vo
    cT
    @97
    cJ
    @116
    @112
    fvtresfn
    eqeq1d
    syl
    @121
    @19
    eqcom
    syl6bb
    rexbiia
    3bitr4ri
    bitri
    eqriv
    @98
    @66
    @0
    @99
    f1oeq3
    ax-mp
    @102
    @99
    @69
    wceq
    @114
    @73
    wb
    @113
    vo
    cT
    @0
    @8
    resmpt
    @0
    @66
    @99
    @69
    f1oeq1
    mp2b
    bitri
    mpbi
    #
    @0
    @66
    @64
    @68
    @69
    f1oco
    mp2an
    wtru
    @0
    @0
    cH
    @64
    @53
    @70
    wtru
    @70
    @53
    wtru
    vo
    vf
    @0
    @66
    @8
    @67
    @9
    @69
    @68
    @8
    @66
    wcel
    vo
    @0
    wral
    #
    wtru
    @73
    @0
    @66
    @69
    wf
    #
    @129
    @128
    @0
    @66
    @69
    f1of
    @129
    @130
    vo
    @0
    @66
    @8
    @69
    @69
    eqid
    fmpt
    biimpri
    mp2b
    a1i
    wtru
    @69
    eqidd
    wtru
    @68
    eqidd
    @19
    @8
    cbits
    coeq2
    fmptcof
    eqcomd
    wtru
    @0
    eqidd
    cH
    @64
    wceq
    wtru
    eulerpart.h
    a1i
    f1oeq123d
    mpbiri
    #
    trud
    @0
    cH
    @44
    cM
    @53
    f1oco
    mp2an
    @54
    @48
    wceq
    #
    @55
    @52
    wb
    @132
    wtru
    vo
    vr
    @0
    cH
    @9
    @59
    cM
    cfv
    #
    @10
    @53
    cM
    wtru
    @7
    @0
    wcel
    #
    wa
    #
    @7
    @53
    cfv
    @9
    cH
    wtru
    vo
    @0
    @9
    @53
    cvv
    wtru
    @53
    eqidd
    #
    @9
    cvv
    wcel
    @135
    cbits
    @8
    cz
    @61
    cbits
    wf
    cz
    cvv
    wcel
    cbits
    cvv
    wcel
    bitsf
    zex
    cz
    @61
    cvv
    cbits
    fex
    mp2an
    @120
    coex
    a1i
    fvmpt2d
    wtru
    @0
    cH
    @7
    @53
    wtru
    @57
    @0
    cH
    @53
    wf
    @131
    @0
    cH
    @53
    f1of
    syl
    ffvelrnda
    eqeltrrd
    @136
    cM
    vr
    cH
    @133
    cmpt
    wceq
    #
    wtru
    cM
    cH
    wfn
    #
    @137
    @56
    @138
    @58
    cH
    @44
    cM
    f1ofn
    ax-mp
    vr
    cH
    cM
    dffn5
    mpbi
    a1i
    @59
    @9
    cM
    fveq2
    fmptco
    trud
    @0
    @44
    @54
    @48
    f1oeq1
    ax-mp
    mpbi
    #
    @0
    @44
    @16
    @47
    @48
    f1oco
    mp2an
    @49
    @12
    wceq
    #
    @50
    @18
    wb
    @140
    wtru
    vo
    va
    @0
    @44
    @10
    @46
    @11
    @48
    @47
    @135
    @7
    @48
    cfv
    #
    @10
    @44
    @135
    @134
    @10
    cvv
    wcel
    @141
    @10
    wceq
    wtru
    @134
    simpr
    #
    @9
    cM
    fvex
    vo
    @0
    @10
    cvv
    @48
    @48
    eqid
    fvmpt2
    sylancl
    wtru
    @0
    @44
    @7
    @48
    @52
    @0
    @44
    @48
    wf
    wtru
    @139
    @0
    @44
    @48
    f1of
    mp1i
    ffvelrnda
    eqeltrrd
    wtru
    @48
    eqidd
    wtru
    @47
    eqidd
    @45
    @10
    cF
    imaeq2
    fmptco
    trud
    @0
    @16
    @49
    @12
    f1oeq1
    ax-mp
    mpbi
    #
    @0
    @16
    @3
    @6
    @12
    f1oco
    mp2an
    cG
    @13
    wceq
    @4
    @14
    wb
    cG
    vo
    @0
    @11
    @5
    cfv
    #
    cmpt
    #
    @13
    eulerpart.g
    @13
    @145
    wceq
    wtru
    vo
    vb
    @0
    @16
    @11
    vb
    cv
    #
    @5
    cfv
    #
    @144
    @12
    @6
    @135
    @7
    @12
    cfv
    #
    @11
    @16
    @135
    @134
    @11
    cvv
    wcel
    #
    @148
    @11
    wceq
    @142
    cF
    cvv
    wcel
    #
    @149
    @78
    @81
    @150
    @80
    nn0ex
    vx
    vy
    cJ
    cn0
    c2
    vy
    cv
    cexp
    co
    vx
    cv
    cmul
    co
    cvv
    cvv
    cF
    eulerpart.f
    mpt2exg
    mp2an
    cF
    @10
    cvv
    imaexg
    ax-mp
    vo
    @0
    @11
    cvv
    @12
    @12
    eqid
    fvmpt2
    sylancl
    wtru
    @0
    @16
    @7
    @12
    @18
    @0
    @16
    @12
    wf
    wtru
    @143
    @0
    @16
    @12
    f1of
    mp1i
    ffvelrnda
    eqeltrrd
    wtru
    @12
    eqidd
    @6
    vb
    @16
    @147
    cmpt
    #
    wceq
    wtru
    @6
    vb
    @15
    @147
    cmpt
    #
    cfn
    cres
    @151
    @5
    @152
    cfn
    @5
    @15
    wfn
    #
    @5
    @152
    wceq
    @26
    @15
    @2
    @5
    wf1o
    @153
    nnex
    cn
    cvv
    indf1o
    @15
    @2
    @5
    f1ofn
    mp2b
    vb
    @15
    @5
    dffn5
    mpbi
    reseq1i
    vb
    @15
    cfn
    @147
    resmpt3
    eqtri
    a1i
    @146
    @11
    @5
    fveq2
    fmptco
    trud
    eqtr4i
    @0
    @3
    cG
    @13
    f1oeq1
    ax-mp
    mpbir
end
