include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "crab.mm"
include "chash.mm"
include "cc0.mm"
include "cpr.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "c2.mm"
include "cexp.mm"
include "cle.mm"
include "wbr.mm"
include "cdom.mm"
include "cvv.mm"
include "wcel.mm"
include "ovex.mm"
include "cprime.mm"
include "cpc.mm"
include "cif.mm"
include "cmpt.mm"
include "wa.mm"
include "weq.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "wf.mm"
include "caddc.mm"
include "clt.mm"
include "wn.mm"
include "cdiv.mm"
include "cdvds.mm"
include "cn.mm"
include "cuz.mm"
include "cdif.mm"
include "wral.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "simprl.mm"
include "ad2antrr.mm"
include "sseldi.mm"
include "elfznn.mm"
include "syl.mm"
include "simpr.mm"
include "prmuz2.mm"
include "wi.mm"
include "prmreclem1.mm"
include "simp3d.mm"
include "sylc.mm"
include "simprr.mm"
include "oveq1d.mm"
include "sq1.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "nncnd.mm"
include "div1d.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "cz.mm"
include "cn0.mm"
include "wb.mm"
include "nnzd.mm"
include "2nn0.mm"
include "a1i.mm"
include "pcdvdsb.mm"
include "syl3anc.mm"
include "bitr4d.mm"
include "mtbid.mm"
include "cr.mm"
include "pccld.mm"
include "nn0red.mm"
include "2re.mm"
include "ltnle.mm"
include "sylancl.mm"
include "mpbird.mm"
include "df-2.mm"
include "syl6breq.mm"
include "nn0zd.mm"
include "1z.mm"
include "zleltp1.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "elfz5.mm"
include "0z.mm"
include "fzpr.mm"
include "ax-mp.mm"
include "1e0p1.mm"
include "oveq2i.mm"
include "preq2i.mm"
include "3eqtr4i.mm"
include "c0ex.mm"
include "prid1.mm"
include "ifclda.mm"
include "eqid.mm"
include "fmptd.mm"
include "prex.mm"
include "elmap.mm"
include "sylibr.mm"
include "ex.mm"
include "syl5bi.mm"
include "anbi12i.mm"
include "wfn.mm"
include "ifex.mm"
include "fnmpti.mm"
include "eqfnfv.mm"
include "mp2an.mm"
include "eleq1.mm"
include "oveq1.mm"
include "ifbieq1d.mm"
include "fvmpt.mm"
include "eqeq12d.mm"
include "ralbiia.mm"
include "bitri.mm"
include "cin.mm"
include "simprll.mm"
include "breq2.mm"
include "notbid.mm"
include "ralbidv.mm"
include "elrab2.mm"
include "simprbi.mm"
include "simprrl.mm"
include "r19.26.mm"
include "eldifi.mm"
include "fz1ssnn.mm"
include "sstri.mm"
include "pceq0.mm"
include "syl2anr.mm"
include "anbi12d.mm"
include "eqtr3.mm"
include "syl6bir.mm"
include "ralimdva.mm"
include "syl5bir.mm"
include "mp2and.mm"
include "biantrud.mm"
include "cun.mm"
include "incom.mm"
include "uneq1i.mm"
include "inundif.mm"
include "eqtri.mm"
include "raleqi.mm"
include "ralunb.mm"
include "bitr3i.mm"
include "eldifn.mm"
include "iffalse.mm"
include "eqtr4d.mm"
include "rgen.mm"
include "biantru.mm"
include "elinel1.mm"
include "iftrue.mm"
include "3bitr4g.mm"
include "nnnn0d.mm"
include "pc11.mm"
include "syl2anc.mm"
include "syl5bb.mm"
include "dom2d.mm"
include "mpi.mm"
include "cfn.mm"
include "wss.mm"
include "fzfi.mm"
include "ssfi.mm"
include "eqeltri.mm"
include "prfi.mm"
include "fzfid.mm"
include "mapfi.mm"
include "sylancr.mm"
include "hashdom.mm"
include "hashmap.mm"
include "prhash2ex.mm"
include "hashfz1.mm"
include "oveq12d.mm"
include "breqtrd.mm"

theorem prmreclem2
  let wph: wff ph
  let vx: setvar x
  let cQ: class Q
  let vn: setvar n
  let cF: class F
  let cK: class K
  let cM: class M
  let cN: class N
  let vr: setvar r
  let vp: setvar p
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vq: setvar q
  let cA: class A
  let cW: class W
  assume prmrec.1: |- F = ( n e. NN |-> if ( n e. Prime , ( 1 / n ) , 0 ) )
  assume prmrec.2: |- ( ph -> K e. NN )
  assume prmrec.3: |- ( ph -> N e. NN )
  assume prmrec.4: |- M = { n e. ( 1 ... N ) | A. p e. ( Prime \ ( 1 ... K ) ) -. p || n }
  assume prmreclem2.5: |- Q = ( n e. NN |-> sup ( { r e. NN | ( r ^ 2 ) || n } , RR , < ) )

  disjoint n p
  disjoint n r
  disjoint n x
  disjoint F n
  disjoint p r
  disjoint p x
  disjoint F p
  disjoint r x
  disjoint F r
  disjoint F x
  disjoint K n
  disjoint K p
  disjoint K x
  disjoint M n
  disjoint M p
  disjoint M x
  disjoint n ph
  disjoint p ph
  disjoint ph x
  disjoint Q n
  disjoint Q p
  disjoint Q r
  disjoint Q x
  disjoint N n
  disjoint N p
  disjoint N x
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j p
  disjoint j r
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k r
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint m n
  disjoint m p
  disjoint m r
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n w
  disjoint n y
  disjoint n z
  disjoint p w
  disjoint p y
  disjoint p z
  disjoint r w
  disjoint r y
  disjoint r z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint j q
  disjoint K j
  disjoint k q
  disjoint K k
  disjoint n q
  disjoint p q
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint K q
  disjoint K y
  disjoint K z
  disjoint M k
  disjoint M q
  disjoint M y
  disjoint M z
  disjoint A r
  disjoint j ph
  disjoint k ph
  disjoint ph q
  disjoint ph y
  disjoint ph z
  disjoint Q y
  disjoint Q z
  disjoint W j
  disjoint W k
  disjoint W q
  disjoint W x
  disjoint N j
  disjoint N k
  disjoint N q
  disjoint N y
  disjoint N z
  assert |- ( ph -> ( # ` { x e. M | ( Q ` x ) = 1 } ) <_ ( 2 ^ K ) )

  proof
    wph
    vx
    cv
    #
    cQ
    cfv
    #
    c1
    wceq
    #
    vx
    cM
    crab
    #
    chash
    cfv
    #
    cc0
    c1
    cpr
    #
    c1
    cK
    cfz
    co
    #
    cmap
    co
    #
    chash
    cfv
    #
    c2
    cK
    cexp
    co
    #
    cle
    wph
    @4
    @8
    cle
    wbr
    #
    @3
    @7
    cdom
    wbr
    #
    wph
    @7
    cvv
    wcel
    @11
    @5
    @6
    cmap
    ovex
    wph
    vy
    vz
    @3
    @7
    vn
    @6
    vn
    cv
    #
    cprime
    wcel
    #
    @12
    vy
    cv
    #
    cpc
    co
    #
    cc0
    cif
    #
    cmpt
    #
    vn
    @6
    @13
    @12
    vz
    cv
    #
    cpc
    co
    #
    cc0
    cif
    #
    cmpt
    #
    cvv
    @14
    @3
    wcel
    #
    @14
    cM
    wcel
    #
    @14
    cQ
    cfv
    #
    c1
    wceq
    #
    wa
    #
    wph
    @17
    @7
    wcel
    #
    @2
    @25
    vx
    @14
    cM
    vx
    vy
    weq
    @1
    @24
    c1
    @0
    @14
    cQ
    fveq2
    eqeq1d
    elrab
    #
    wph
    @26
    @27
    wph
    @26
    wa
    #
    @6
    @5
    @17
    wf
    @27
    @29
    vn
    @6
    @16
    @5
    @17
    @29
    @12
    @6
    wcel
    #
    wa
    #
    @13
    @15
    cc0
    @5
    @31
    @13
    wa
    #
    @15
    cc0
    c1
    cfz
    co
    #
    @5
    @32
    @15
    @33
    wcel
    #
    @15
    c1
    cle
    wbr
    #
    @32
    @35
    @15
    c1
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @32
    @15
    c2
    @36
    clt
    @32
    @15
    c2
    clt
    wbr
    #
    c2
    @15
    cle
    wbr
    #
    wn
    #
    @32
    @12
    c2
    cexp
    co
    #
    @14
    @24
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cdvds
    wbr
    #
    @39
    @32
    @14
    cn
    wcel
    #
    @12
    c2
    cuz
    cfv
    wcel
    #
    @44
    wn
    #
    @32
    @14
    c1
    cN
    cfz
    co
    #
    wcel
    #
    @45
    @32
    cM
    @48
    @14
    cM
    vp
    cv
    #
    @12
    cdvds
    wbr
    #
    wn
    #
    vp
    cprime
    @6
    cdif
    #
    wral
    #
    vn
    @48
    crab
    #
    @48
    prmrec.4
    @54
    vn
    @48
    ssrab2
    #
    eqsstri
    #
    @29
    @23
    @30
    @13
    wph
    @23
    @25
    simprl
    ad2antrr
    sseldi
    @14
    cN
    elfznn
    syl
    #
    @32
    @13
    @46
    @31
    @13
    simpr
    #
    @12
    prmuz2
    syl
    @45
    @24
    cn
    wcel
    @42
    @14
    cdvds
    wbr
    @46
    @47
    wi
    cQ
    vn
    @12
    @14
    vr
    prmreclem2.5
    prmreclem1
    simp3d
    sylc
    @32
    @44
    @41
    @14
    cdvds
    wbr
    #
    @39
    @32
    @43
    @14
    @41
    cdvds
    @32
    @43
    @14
    c1
    cdiv
    co
    @14
    @32
    @42
    c1
    @14
    cdiv
    @32
    @42
    c1
    c2
    cexp
    co
    c1
    @32
    @24
    c1
    c2
    cexp
    @29
    @25
    @30
    @13
    wph
    @23
    @25
    simprr
    ad2antrr
    oveq1d
    sq1
    syl6eq
    oveq2d
    @32
    @14
    @32
    @14
    @58
    nncnd
    div1d
    eqtrd
    breq2d
    @32
    @13
    @14
    cz
    wcel
    c2
    cn0
    wcel
    #
    @39
    @60
    wb
    @59
    @32
    @14
    @58
    nnzd
    @61
    @32
    2nn0
    a1i
    c2
    @12
    @14
    pcdvdsb
    syl3anc
    bitr4d
    mtbid
    @32
    @15
    cr
    wcel
    c2
    cr
    wcel
    @38
    @40
    wb
    @32
    @15
    @32
    @12
    @14
    @59
    @58
    pccld
    #
    nn0red
    2re
    @15
    c2
    ltnle
    sylancl
    mpbird
    df-2
    syl6breq
    @32
    @15
    cz
    wcel
    c1
    cz
    wcel
    #
    @35
    @37
    wb
    @32
    @15
    @62
    nn0zd
    1z
    @15
    c1
    zleltp1
    sylancl
    mpbird
    @32
    @15
    cc0
    cuz
    cfv
    #
    wcel
    @63
    @34
    @35
    wb
    @32
    @15
    cn0
    @64
    @62
    nn0uz
    syl6eleq
    1z
    @15
    cc0
    c1
    elfz5
    sylancl
    mpbird
    cc0
    cc0
    c1
    caddc
    co
    #
    cfz
    co
    #
    cc0
    @65
    cpr
    #
    @33
    @5
    cc0
    cz
    wcel
    @66
    @67
    wceq
    0z
    cc0
    fzpr
    ax-mp
    c1
    @65
    cc0
    cfz
    1e0p1
    oveq2i
    c1
    @65
    cc0
    1e0p1
    preq2i
    3eqtr4i
    syl6eleq
    cc0
    @5
    wcel
    @31
    @13
    wn
    wa
    cc0
    c1
    c0ex
    prid1
    a1i
    ifclda
    @17
    eqid
    #
    fmptd
    @5
    @6
    @17
    cc0
    c1
    prex
    c1
    cK
    cfz
    ovex
    elmap
    sylibr
    ex
    syl5bi
    @22
    @18
    @3
    wcel
    #
    wa
    @26
    @18
    cM
    wcel
    #
    @18
    cQ
    cfv
    #
    c1
    wceq
    #
    wa
    #
    wa
    #
    wph
    @17
    @21
    wceq
    #
    vy
    vz
    weq
    #
    wb
    #
    @22
    @26
    @69
    @73
    @28
    @2
    @72
    vx
    @18
    cM
    vx
    vz
    weq
    @1
    @71
    c1
    @0
    @18
    cQ
    fveq2
    eqeq1d
    elrab
    anbi12i
    wph
    @74
    @77
    @75
    @50
    cprime
    wcel
    #
    @50
    @14
    cpc
    co
    #
    cc0
    cif
    #
    @78
    @50
    @18
    cpc
    co
    #
    cc0
    cif
    #
    wceq
    #
    vp
    @6
    wral
    #
    wph
    @74
    wa
    #
    @76
    @75
    @50
    @17
    cfv
    #
    @50
    @21
    cfv
    #
    wceq
    #
    vp
    @6
    wral
    #
    @84
    @17
    @6
    wfn
    @21
    @6
    wfn
    @75
    @89
    wb
    vn
    @6
    @16
    @17
    @13
    @15
    cc0
    @12
    @14
    cpc
    ovex
    c0ex
    ifex
    @68
    fnmpti
    vn
    @6
    @20
    @21
    @13
    @19
    cc0
    @12
    @18
    cpc
    ovex
    c0ex
    ifex
    @21
    eqid
    #
    fnmpti
    vp
    @6
    @17
    @21
    eqfnfv
    mp2an
    @88
    @83
    vp
    @6
    @50
    @6
    wcel
    @86
    @80
    @87
    @82
    vn
    @50
    @16
    @80
    @6
    @17
    vn
    vp
    weq
    #
    @13
    @78
    @15
    @79
    cc0
    @12
    @50
    cprime
    eleq1
    #
    @12
    @50
    @14
    cpc
    oveq1
    ifbieq1d
    @68
    @78
    @79
    cc0
    @50
    @14
    cpc
    ovex
    c0ex
    ifex
    fvmpt
    vn
    @50
    @20
    @82
    @6
    @21
    @91
    @13
    @78
    @19
    @81
    cc0
    @92
    @12
    @50
    @18
    cpc
    oveq1
    ifbieq1d
    @90
    @78
    @81
    cc0
    @50
    @18
    cpc
    ovex
    c0ex
    ifex
    fvmpt
    eqeq12d
    ralbiia
    bitri
    @85
    @84
    @79
    @81
    wceq
    #
    vp
    cprime
    wral
    #
    @76
    @85
    @93
    vp
    cprime
    @6
    cin
    #
    wral
    #
    @96
    @93
    vp
    @53
    wral
    #
    wa
    #
    @84
    @94
    @85
    @97
    @96
    @85
    @50
    @14
    cdvds
    wbr
    #
    wn
    #
    vp
    @53
    wral
    #
    @50
    @18
    cdvds
    wbr
    #
    wn
    #
    vp
    @53
    wral
    #
    @97
    @85
    @23
    @101
    wph
    @23
    @25
    @73
    simprll
    #
    @23
    @49
    @101
    @54
    @101
    vn
    @14
    @48
    cM
    vn
    vy
    weq
    #
    @52
    @100
    vp
    @53
    @106
    @51
    @99
    @12
    @14
    @50
    cdvds
    breq2
    notbid
    ralbidv
    prmrec.4
    elrab2
    simprbi
    syl
    @85
    @70
    @104
    wph
    @26
    @70
    @72
    simprrl
    #
    @70
    @18
    @48
    wcel
    @104
    @54
    @104
    vn
    @18
    @48
    cM
    vn
    vz
    weq
    #
    @52
    @103
    vp
    @53
    @108
    @51
    @102
    @12
    @18
    @50
    cdvds
    breq2
    notbid
    ralbidv
    prmrec.4
    elrab2
    simprbi
    syl
    @101
    @104
    wa
    @100
    @103
    wa
    #
    vp
    @53
    wral
    @85
    @97
    @100
    @103
    vp
    @53
    r19.26
    @85
    @109
    @93
    vp
    @53
    @85
    @50
    @53
    wcel
    #
    wa
    #
    @109
    @79
    cc0
    wceq
    #
    @81
    cc0
    wceq
    #
    wa
    @93
    @111
    @112
    @100
    @113
    @103
    @110
    @78
    @45
    @112
    @100
    wb
    @85
    @50
    cprime
    @6
    eldifi
    #
    @85
    cM
    cn
    @14
    cM
    @48
    cn
    @57
    cN
    fz1ssnn
    sstri
    #
    @105
    sseldi
    #
    @50
    @14
    pceq0
    syl2anr
    @110
    @78
    @18
    cn
    wcel
    @113
    @103
    wb
    @85
    @114
    @85
    cM
    cn
    @18
    @115
    @107
    sseldi
    #
    @50
    @18
    pceq0
    syl2anr
    anbi12d
    @79
    @81
    cc0
    eqtr3
    syl6bir
    ralimdva
    syl5bir
    mp2and
    biantrud
    @84
    @83
    vp
    @95
    wral
    #
    @83
    vp
    @6
    cprime
    cdif
    #
    wral
    #
    wa
    #
    @96
    @84
    @83
    vp
    @95
    @119
    cun
    #
    wral
    @121
    @83
    vp
    @122
    @6
    @122
    @6
    cprime
    cin
    #
    @119
    cun
    @6
    @95
    @123
    @119
    cprime
    @6
    incom
    uneq1i
    @6
    cprime
    inundif
    eqtri
    raleqi
    @83
    vp
    @95
    @119
    ralunb
    bitr3i
    @121
    @118
    @96
    @120
    @118
    @83
    vp
    @119
    @50
    @119
    wcel
    @78
    wn
    #
    @83
    @50
    @6
    cprime
    eldifn
    @124
    @80
    cc0
    @82
    @78
    @79
    cc0
    iffalse
    @78
    @81
    cc0
    iffalse
    eqtr4d
    syl
    rgen
    biantru
    @83
    @93
    vp
    @95
    @50
    @95
    wcel
    @78
    @83
    @93
    wb
    @50
    cprime
    @6
    elinel1
    @78
    @80
    @79
    @82
    @81
    @78
    @79
    cc0
    iftrue
    @78
    @81
    cc0
    iftrue
    eqeq12d
    syl
    ralbiia
    bitr3i
    bitri
    @94
    @93
    vp
    @95
    @53
    cun
    #
    wral
    @98
    @93
    vp
    @125
    cprime
    cprime
    @6
    inundif
    raleqi
    @93
    vp
    @95
    @53
    ralunb
    bitr3i
    3bitr4g
    @85
    @14
    cn0
    wcel
    @18
    cn0
    wcel
    @76
    @94
    wb
    @85
    @14
    @116
    nnnn0d
    @85
    @18
    @117
    nnnn0d
    @14
    @18
    vp
    pc11
    syl2anc
    bitr4d
    syl5bb
    ex
    syl5bi
    dom2d
    mpi
    wph
    @3
    cfn
    wcel
    #
    @7
    cfn
    wcel
    #
    @10
    @11
    wb
    cM
    cfn
    wcel
    @3
    cM
    wss
    @126
    cM
    @55
    cfn
    prmrec.4
    @48
    cfn
    wcel
    @55
    @48
    wss
    @55
    cfn
    wcel
    c1
    cN
    fzfi
    @56
    @48
    @55
    ssfi
    mp2an
    eqeltri
    @2
    vx
    cM
    ssrab2
    cM
    @3
    ssfi
    mp2an
    wph
    @5
    cfn
    wcel
    #
    @6
    cfn
    wcel
    #
    @127
    cc0
    c1
    prfi
    #
    wph
    c1
    cK
    fzfid
    #
    @5
    @6
    mapfi
    sylancr
    @3
    @7
    cfn
    hashdom
    sylancr
    mpbird
    wph
    @8
    @5
    chash
    cfv
    #
    @6
    chash
    cfv
    #
    cexp
    co
    #
    @9
    wph
    @128
    @129
    @8
    @134
    wceq
    @130
    @131
    @5
    @6
    hashmap
    sylancr
    wph
    @132
    c2
    @133
    cK
    cexp
    @132
    c2
    wceq
    wph
    prhash2ex
    a1i
    wph
    cK
    cn0
    wcel
    @133
    cK
    wceq
    wph
    cK
    prmrec.2
    nnnn0d
    cK
    hashfz1
    syl
    oveq12d
    eqtrd
    breqtrd
end
