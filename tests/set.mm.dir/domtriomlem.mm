include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "cv.mm"
include "cfv.mm"
include "com.mm"
include "wral.mm"
include "wex.mm"
include "cdom.mm"
include "wbr.mm"
include "wfn.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "wa.mm"
include "wss.mm"
include "cpw.mm"
include "cen.mm"
include "cab.mm"
include "cvv.mm"
include "pwex.mm"
include "simpl.mm"
include "ss2abi.mm"
include "df-pw.mm"
include "sseqtr4i.mm"
include "ssexi.mm"
include "eqeltri.mm"
include "omex.mm"
include "enref.mm"
include "axcc3.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "ccrd.mm"
include "nnfi.mm"
include "pwfi.mm"
include "sylib.mm"
include "ficardom.mm"
include "isinf.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "rspcv.mm"
include "syl5.mm"
include "3syl.mm"
include "cdm.mm"
include "finnum.mm"
include "cardid2.mm"
include "entr.mm"
include "expcom.mm"
include "4syl.mm"
include "anim2d.mm"
include "eximdv.mm"
include "syld.mm"
include "neeq1i.mm"
include "abn0.mm"
include "bitri.mm"
include "syl6ibr.mm"
include "com12.mm"
include "adantr.mm"
include "rsp.mm"
include "adantl.mm"
include "mpdd.mm"
include "ralrimi.mm"
include "3adant2.mm"
include "3expib.mm"
include "mpi.mm"
include "axcc2.mm"
include "w3a.mm"
include "simp2.mm"
include "fvex.mm"
include "sseq1.mm"
include "breq1.mm"
include "anbi12d.mm"
include "elab2.mm"
include "simprbi.mm"
include "ralimi.mm"
include "ciun.mm"
include "cdif.mm"
include "weq.mm"
include "fveq2.mm"
include "pweq.mm"
include "breq12d.mm"
include "cbvralv.mm"
include "csdm.mm"
include "csuc.mm"
include "peano2.mm"
include "omelon.mm"
include "onelssi.mm"
include "ssralv.mm"
include "pwsdompw.mm"
include "ex.mm"
include "sdomdif.mm"
include "syl6.mm"
include "syl5bi.mm"
include "difss.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "neeq1d.mm"
include "sylibrd.mm"
include "syl5com.mm"
include "jca.mm"
include "wf1.mm"
include "wf.mm"
include "eleq2d.mm"
include "eldifi.mm"
include "syl6bi.mm"
include "simplbi.mm"
include "sseld.mm"
include "syl9.mm"
include "com23.mm"
include "com13.mm"
include "imp.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "wel.mm"
include "w3o.mm"
include "word.mm"
include "nnord.mm"
include "ordtri3or.mm"
include "syl2an.mm"
include "cbviunv.mm"
include "iuneq1.mm"
include "syl5eq.mm"
include "difeq12d.mm"
include "eleq12d.mm"
include "rspccv.mm"
include "mpbidi.mm"
include "syl11.mm"
include "3ad2ant1.mm"
include "eleq1.mm"
include "syl5ib.mm"
include "3ad2ant3.mm"
include "ssiun2.mm"
include "3impib.mm"
include "3ad2ant2.mm"
include "eldifbd.mm"
include "3adant1.mm"
include "pm2.21dd.mm"
include "3exp.mm"
include "2a1.mm"
include "ssiun2s.mm"
include "eldifn.mm"
include "a1i.mm"
include "3imp.mm"
include "3jaoi.mm"
include "3expia.mm"
include "mpid.mm"
include "com3r.mm"
include "expd.mm"
include "ralrimd.mm"
include "ralrimiv.mm"
include "dff13.mm"
include "19.8a.mm"
include "syl.mm"
include "brdom.mm"
include "sylibr.mm"
include "exlimdv.mm"
include "mpd.mm"
include "exlimiv.mm"

theorem domtriomlem
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vn: setvar n
  let vb: setvar b
  let vc: setvar c
  let vm: setvar m
  let vj: setvar j
  assume domtriomlem.1: |- A e. _V
  assume domtriomlem.2: |- B = { y | ( y C_ A /\ y ~~ ~P n ) }
  assume domtriomlem.3: |- C = ( n e. _om |-> ( ( b ` n ) \ U_ k e. n ( b ` k ) ) )

  disjoint A b
  disjoint A n
  disjoint b n
  disjoint A y
  disjoint n y
  disjoint B b
  disjoint C k
  disjoint C n
  disjoint k n
  disjoint b k
  disjoint b y
  disjoint A c
  disjoint b c
  disjoint c n
  disjoint A m
  disjoint m n
  disjoint m y
  disjoint B c
  disjoint C c
  disjoint c k
  disjoint b j
  disjoint j k
  disjoint j n
  assert |- ( -. A e. Fin -> _om ~<_ A )

  proof
    cA
    cfn
    wcel
    wn
    #
    vn
    cv
    #
    vb
    cv
    #
    cfv
    #
    cB
    wcel
    #
    vn
    com
    wral
    #
    vb
    wex
    #
    com
    cA
    cdom
    wbr
    #
    @0
    @2
    com
    wfn
    #
    cB
    c0
    wne
    #
    @4
    wi
    #
    vn
    com
    wral
    #
    wa
    #
    vb
    wex
    @6
    vb
    vn
    cB
    com
    cB
    vy
    cv
    #
    cA
    wss
    #
    @13
    @1
    cpw
    #
    cen
    wbr
    #
    wa
    #
    vy
    cab
    #
    cvv
    domtriomlem.2
    @18
    cA
    cpw
    #
    cA
    domtriomlem.1
    pwex
    @18
    @14
    vy
    cab
    @19
    @17
    @14
    vy
    @14
    @16
    simpl
    ss2abi
    vy
    cA
    df-pw
    sseqtr4i
    ssexi
    eqeltri
    com
    omex
    enref
    axcc3
    @0
    @12
    @5
    vb
    @0
    @8
    @11
    @5
    @0
    @11
    @5
    @8
    @0
    @11
    wa
    #
    @4
    vn
    com
    @0
    @11
    vn
    @0
    vn
    nfv
    @10
    vn
    com
    nfra1
    nfan
    @20
    @1
    com
    wcel
    #
    @9
    @4
    @0
    @21
    @9
    wi
    @11
    @21
    @0
    @9
    @21
    @0
    @17
    vy
    wex
    #
    @9
    @21
    @0
    @14
    @13
    @15
    ccrd
    cfv
    #
    cen
    wbr
    #
    wa
    #
    vy
    wex
    #
    @22
    @21
    @15
    cfn
    wcel
    #
    @23
    com
    wcel
    #
    @0
    @26
    wi
    @21
    @1
    cfn
    wcel
    @27
    @1
    nnfi
    @1
    pwfi
    sylib
    #
    @15
    ficardom
    @0
    @14
    @13
    vm
    cv
    #
    cen
    wbr
    #
    wa
    #
    vy
    wex
    #
    vm
    com
    wral
    @28
    @26
    vy
    cA
    vm
    isinf
    @33
    @26
    vm
    @23
    com
    @30
    @23
    wceq
    #
    @32
    @25
    vy
    @34
    @31
    @24
    @14
    @30
    @23
    @13
    cen
    breq2
    anbi2d
    exbidv
    rspcv
    syl5
    3syl
    @21
    @25
    @17
    vy
    @21
    @24
    @16
    @14
    @21
    @27
    @15
    ccrd
    cdm
    wcel
    @23
    @15
    cen
    wbr
    #
    @24
    @16
    wi
    @29
    @15
    finnum
    @15
    cardid2
    @24
    @35
    @16
    @13
    @23
    @15
    entr
    expcom
    4syl
    anim2d
    eximdv
    syld
    @9
    @18
    c0
    wne
    @22
    cB
    @18
    c0
    domtriomlem.2
    neeq1i
    @17
    vy
    abn0
    bitri
    syl6ibr
    com12
    adantr
    @11
    @21
    @10
    wi
    @0
    @10
    vn
    com
    rsp
    adantl
    mpdd
    ralrimi
    3adant2
    3expib
    eximdv
    mpi
    @5
    @7
    vb
    @5
    vc
    cv
    #
    com
    wfn
    #
    @1
    @36
    cfv
    #
    @1
    cC
    cfv
    #
    wcel
    #
    vn
    com
    wral
    #
    wa
    #
    vc
    wex
    #
    @7
    @5
    @37
    @39
    c0
    wne
    #
    @40
    wi
    #
    vn
    com
    wral
    #
    wa
    #
    vc
    wex
    @43
    vc
    vn
    cC
    axcc2
    @5
    @47
    @42
    vc
    @5
    @37
    @46
    @42
    @5
    @37
    @46
    w3a
    @37
    @41
    @5
    @37
    @46
    simp2
    @5
    @46
    @41
    @37
    @5
    @46
    wa
    #
    @40
    vn
    com
    @5
    @46
    vn
    @4
    vn
    com
    nfra1
    #
    @45
    vn
    com
    nfra1
    nfan
    @48
    @21
    @44
    @40
    @5
    @21
    @44
    wi
    @46
    @5
    @3
    @15
    cen
    wbr
    #
    vn
    com
    wral
    #
    @21
    @44
    @4
    @50
    vn
    com
    @4
    @3
    cA
    wss
    #
    @50
    @17
    @52
    @50
    wa
    vy
    @3
    cB
    @1
    @2
    fvex
    #
    @13
    @3
    wceq
    @14
    @52
    @16
    @50
    @13
    @3
    cA
    sseq1
    @13
    @3
    @15
    cen
    breq1
    anbi12d
    domtriomlem.2
    elab2
    #
    simprbi
    ralimi
    @21
    @51
    @3
    vk
    @1
    vk
    cv
    #
    @2
    cfv
    #
    ciun
    #
    cdif
    #
    c0
    wne
    #
    @44
    @51
    @56
    @55
    cpw
    #
    cen
    wbr
    #
    vk
    com
    wral
    #
    @21
    @59
    @50
    @61
    vn
    vk
    com
    vn
    vk
    weq
    #
    @3
    @56
    @15
    @60
    cen
    @1
    @55
    @2
    fveq2
    #
    @1
    @55
    pweq
    breq12d
    cbvralv
    @21
    @62
    @57
    @3
    csdm
    wbr
    #
    @59
    @21
    @62
    @61
    vk
    @1
    csuc
    #
    wral
    #
    @65
    @21
    @66
    com
    wcel
    @66
    com
    wss
    @62
    @67
    wi
    @1
    peano2
    com
    @66
    omelon
    onelssi
    @61
    vk
    @66
    com
    ssralv
    3syl
    @21
    @67
    @65
    @2
    vk
    vn
    pwsdompw
    ex
    syld
    @57
    @3
    sdomdif
    syl6
    syl5bi
    @21
    @39
    @58
    c0
    @21
    @58
    cvv
    wcel
    @39
    @58
    wceq
    @58
    @3
    @53
    @3
    @57
    difss
    ssexi
    vn
    com
    @58
    cvv
    cC
    domtriomlem.3
    fvmpt2
    mpan2
    #
    neeq1d
    sylibrd
    syl5com
    adantr
    @46
    @21
    @45
    wi
    @5
    @45
    vn
    com
    rsp
    adantl
    mpdd
    ralrimi
    3adant2
    jca
    3expib
    eximdv
    mpi
    @5
    @42
    @7
    vc
    @5
    @37
    @41
    @7
    @5
    @37
    @41
    w3a
    #
    com
    cA
    @36
    wf1
    #
    vc
    wex
    #
    @7
    @69
    @70
    @71
    @69
    com
    cA
    @36
    wf
    #
    @55
    @36
    cfv
    #
    @38
    wceq
    #
    vk
    vn
    weq
    #
    wi
    #
    vn
    com
    wral
    #
    vk
    com
    wral
    #
    @70
    @69
    @37
    @38
    cA
    wcel
    #
    vn
    com
    wral
    #
    @72
    @5
    @37
    @41
    simp2
    @5
    @41
    @80
    @37
    @5
    @41
    wa
    @79
    vn
    com
    @5
    @41
    vn
    @49
    @40
    vn
    com
    nfra1
    #
    nfan
    @5
    @41
    @21
    @79
    wi
    @21
    @41
    @5
    @79
    @21
    @41
    @40
    @5
    @79
    wi
    @41
    @21
    @40
    @40
    vn
    com
    rsp
    #
    com12
    @21
    @5
    @40
    @79
    @21
    @5
    @4
    @40
    @79
    wi
    @5
    @21
    @4
    @4
    vn
    com
    rsp
    com12
    @21
    @40
    @38
    @3
    wcel
    #
    @4
    @79
    @21
    @40
    @38
    @58
    wcel
    #
    @83
    @21
    @39
    @58
    @38
    @68
    eleq2d
    #
    @38
    @3
    @57
    eldifi
    #
    syl6bi
    @4
    @3
    cA
    @38
    @4
    @52
    @50
    @54
    simplbi
    sseld
    syl9
    syld
    com23
    syld
    com13
    imp
    ralrimi
    3adant2
    vn
    com
    cA
    @36
    ffnfv
    sylanbrc
    @41
    @5
    @78
    @37
    @41
    @77
    vk
    com
    @41
    @55
    com
    wcel
    #
    @76
    vn
    com
    @81
    @87
    vn
    nfv
    @41
    @87
    @21
    @76
    @87
    @21
    wa
    #
    @74
    @41
    @75
    @88
    @74
    vk
    vn
    wel
    #
    @75
    vn
    vk
    wel
    #
    w3o
    #
    @41
    @75
    wi
    #
    @87
    @55
    word
    @1
    word
    @91
    @21
    @55
    nnord
    @1
    nnord
    @55
    @1
    ordtri3or
    syl2an
    @87
    @21
    @74
    @91
    @92
    wi
    @91
    @87
    @21
    @74
    w3a
    #
    @92
    @89
    @93
    @92
    wi
    @75
    @90
    @89
    @93
    @41
    @75
    @89
    @93
    @41
    w3a
    @38
    @57
    wcel
    #
    @75
    @89
    @93
    @41
    @94
    @93
    @41
    wa
    #
    @38
    @56
    wcel
    #
    @89
    @94
    @93
    @41
    @96
    @93
    @41
    @73
    @56
    vj
    @55
    vj
    cv
    #
    @2
    cfv
    #
    ciun
    #
    cdif
    #
    wcel
    #
    @96
    @87
    @21
    @41
    @101
    wi
    @74
    @84
    vn
    com
    wral
    @87
    @101
    @41
    @84
    @101
    vn
    @55
    com
    @63
    @38
    @73
    @58
    @100
    @1
    @55
    @36
    fveq2
    @63
    @3
    @56
    @57
    @99
    @64
    @63
    @57
    vj
    @1
    @98
    ciun
    @99
    vk
    vj
    @1
    @56
    @98
    @55
    @97
    @2
    fveq2
    cbviunv
    vj
    @1
    @55
    @98
    iuneq1
    syl5eq
    difeq12d
    eleq12d
    rspccv
    @41
    @84
    vn
    com
    @81
    @21
    @40
    @84
    @41
    @82
    @85
    mpbidi
    #
    ralrimi
    syl11
    3ad2ant1
    #
    @74
    @87
    @101
    @96
    wi
    @21
    @101
    @73
    @56
    wcel
    @74
    @96
    @73
    @56
    @99
    eldifi
    @73
    @38
    @56
    eleq1
    syl5ib
    3ad2ant3
    syld
    imp
    @89
    @56
    @57
    @38
    vk
    @1
    @56
    ssiun2
    sseld
    syl5
    3impib
    @93
    @41
    @94
    wn
    @89
    @95
    @38
    @3
    @57
    @93
    @41
    @84
    @21
    @87
    @41
    @84
    wi
    @74
    @41
    @21
    @84
    @102
    com12
    3ad2ant2
    imp
    #
    eldifbd
    3adant1
    pm2.21dd
    3exp
    @75
    @93
    @41
    2a1
    @90
    @93
    @41
    @75
    @90
    @93
    @41
    w3a
    @38
    @99
    wcel
    #
    @75
    @90
    @93
    @41
    @105
    @95
    @84
    @90
    @105
    @104
    @84
    @83
    @90
    @105
    @86
    @90
    @3
    @99
    @38
    vj
    @55
    @98
    @1
    @3
    @97
    @1
    @2
    fveq2
    ssiun2s
    sseld
    syl5
    syl5
    3impib
    @90
    @93
    @41
    @105
    wn
    #
    @93
    @41
    @106
    wi
    wi
    @90
    @93
    @41
    @101
    @106
    @103
    @74
    @87
    @101
    @106
    wi
    @21
    @74
    @101
    @38
    @100
    wcel
    @106
    @73
    @38
    @100
    eleq1
    @38
    @56
    @99
    eldifn
    syl6bi
    3ad2ant3
    syld
    a1i
    3imp
    pm2.21dd
    3exp
    3jaoi
    com12
    3expia
    mpid
    com3r
    expd
    ralrimd
    ralrimiv
    3ad2ant3
    vk
    vn
    com
    cA
    @36
    dff13
    sylanbrc
    @70
    vc
    19.8a
    syl
    com
    cA
    vc
    domtriomlem.1
    brdom
    sylibr
    3expib
    exlimdv
    mpd
    exlimiv
    syl
end
