include "cn.mm"
include "citg1.mm"
include "cfv.mm"
include "cmpt.mm"
include "crn.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "ccnv.mm"
include "cima.mm"
include "cvol.mm"
include "cmul.mm"
include "co.mm"
include "csu.mm"
include "cli.mm"
include "cin.mm"
include "c1.mm"
include "cvv.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "cdm.mm"
include "i1frn.mm"
include "syl.mm"
include "difss.mm"
include "ssfi.mm"
include "sylancl.mm"
include "wa.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "covol.mm"
include "wceq.mm"
include "i1fima.mm"
include "ad2antrr.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "inmbl.mm"
include "syl2anc.mm"
include "mblvol.mm"
include "inss1.mm"
include "a1i.mm"
include "mblss.mm"
include "i1fima2sn.mm"
include "sylan.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "ovolsscl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "eqid.mm"
include "fmptd.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "sslin.mm"
include "wf.mm"
include "peano2nn.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "ovolss.mm"
include "3brtr4d.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "ineq2d.mm"
include "fveq2d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "breq12d.mm"
include "ralbiia.mm"
include "oveq1.mm"
include "cbvralv.mm"
include "bitr4i.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "wrex.mm"
include "sylancr.mm"
include "breq1d.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "climsup.mm"
include "cuni.mm"
include "cxr.mm"
include "inex2.mm"
include "sseq12d.mm"
include "volsup.mm"
include "ciun.mm"
include "iuneq2i.mm"
include "cbviunv.mm"
include "iunin2.mm"
include "3eqtr2i.mm"
include "wfn.mm"
include "ffn.mm"
include "fniunfv.mm"
include "3syl.mm"
include "eqtrd.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eq.mm"
include "eqtr3d.mm"
include "c0.mm"
include "wne.mm"
include "frn.mm"
include "fdm.mm"
include "1nn.mm"
include "ne0i.mm"
include "mp1i.mm"
include "eqnetrd.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "wb.mm"
include "breq1.mm"
include "ralrn.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "supxrre.mm"
include "ccom.mm"
include "rnco2.mm"
include "eqidd.mm"
include "cpnf.mm"
include "cicc.mm"
include "volf.mm"
include "feqmptd.mm"
include "fmptco.mm"
include "rneqd.mm"
include "syl5reqr.mm"
include "supeq1d.mm"
include "3eqtr4d.mm"
include "breqtrrd.mm"
include "i1ff.mm"
include "ssdifssd.mm"
include "sselda.mm"
include "recnd.mm"
include "nnex.mm"
include "mptex.mm"
include "oveq2d.mm"
include "ovex.mm"
include "eqtr4d.mm"
include "adantl.mm"
include "climmulc2.mm"
include "cc.mm"
include "remulcld.mm"
include "anasss.mm"
include "i1fres.mm"
include "cif.mm"
include "fnfvelrn.mm"
include "i1f0rn.mm"
include "ifcld.mm"
include "ssdif.mm"
include "ssdifd.mm"
include "itg1val2.mm"
include "syl13anc.mm"
include "wal.mm"
include "c0ex.mm"
include "ifex.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "eqeq1d.mm"
include "eldifsni.mm"
include "ad2antlr.mm"
include "neeq1.mm"
include "syl5ibrcom.mm"
include "iffalse.mm"
include "necon1ai.mm"
include "syl6.mm"
include "pm4.71rd.mm"
include "bitrd.mm"
include "iftrue.mm"
include "pm5.32i.mm"
include "ancom.mm"
include "bitri.mm"
include "syl6bb.mm"
include "pm5.32da.mm"
include "anass.mm"
include "syl6bbr.mm"
include "fniniseg.mm"
include "elin.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "3bitr4d.mm"
include "alrimiv.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfcnv.mm"
include "nfcv.mm"
include "nfima.mm"
include "cleqf.mm"
include "sumeq2dv.mm"
include "mpteq2dva.mm"
include "fveq1d.mm"
include "sumeq2sdv.mm"
include "sumex.mm"
include "sylan9eq.mm"
include "climfsum.mm"
include "itg1val.mm"

theorem itg1climres
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vj: setvar j
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume itg1climres.1: |- ( ph -> A : NN --> dom vol )
  assume itg1climres.2: |- ( ( ph /\ n e. NN ) -> ( A ` n ) C_ ( A ` ( n + 1 ) ) )
  assume itg1climres.3: |- ( ph -> U. ran A = RR )
  assume itg1climres.4: |- ( ph -> F e. dom S.1 )
  assume itg1climres.5: |- G = ( x e. RR |-> if ( x e. ( A ` n ) , ( F ` x ) , 0 ) )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint F n
  disjoint F x
  disjoint n ph
  disjoint ph x
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint j k
  disjoint F j
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint F y
  disjoint F z
  disjoint G j
  disjoint G k
  disjoint G y
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> ( n e. NN |-> ( S.1 ` G ) ) ~~> ( S.1 ` F ) )

  proof
    wph
    vn
    cn
    cG
    citg1
    cfv
    #
    cmpt
    #
    cF
    crn
    #
    cc0
    csn
    #
    cdif
    #
    vk
    cv
    #
    cF
    ccnv
    @5
    csn
    #
    cima
    #
    cvol
    cfv
    #
    cmul
    co
    #
    vk
    csu
    #
    cF
    citg1
    cfv
    #
    cli
    wph
    @4
    @9
    vk
    vj
    vn
    cn
    @5
    @7
    vn
    cv
    #
    cA
    cfv
    #
    cin
    #
    cvol
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    @1
    c1
    cvv
    cn
    nnuz
    wph
    1zzd
    wph
    @2
    cfn
    wcel
    #
    @4
    @2
    wss
    @4
    cfn
    wcel
    #
    wph
    cF
    citg1
    cdm
    #
    wcel
    #
    @18
    itg1climres.4
    cF
    i1frn
    syl
    @2
    @3
    difss
    @2
    @4
    ssfi
    sylancl
    #
    wph
    @5
    @4
    wcel
    #
    wa
    #
    @8
    @5
    vj
    vn
    cn
    @15
    cmpt
    #
    @17
    c1
    cvv
    cn
    nnuz
    @24
    1zzd
    #
    @24
    @25
    @25
    crn
    #
    cr
    clt
    csup
    #
    @8
    cli
    @24
    vx
    vj
    @25
    c1
    cn
    nnuz
    @26
    @24
    vn
    cn
    @15
    cr
    @25
    @24
    @12
    cn
    wcel
    #
    wa
    #
    @15
    @14
    covol
    cfv
    #
    cr
    @30
    @14
    cvol
    cdm
    #
    wcel
    #
    @15
    @31
    wceq
    @30
    @7
    @32
    wcel
    #
    @13
    @32
    wcel
    #
    @33
    wph
    @34
    @23
    @29
    wph
    @21
    @34
    itg1climres.4
    @6
    cF
    i1fima
    syl
    #
    ad2antrr
    #
    wph
    @29
    @35
    @23
    wph
    cn
    @32
    @12
    cA
    itg1climres.1
    ffvelrnda
    #
    adantlr
    @7
    @13
    inmbl
    syl2anc
    #
    @14
    mblvol
    syl
    #
    @30
    @14
    @7
    wss
    #
    @7
    cr
    wss
    #
    @7
    covol
    cfv
    #
    cr
    wcel
    @31
    cr
    wcel
    @41
    @30
    @7
    @13
    inss1
    #
    a1i
    @30
    @34
    @42
    @37
    @7
    mblss
    #
    syl
    #
    @30
    @8
    @43
    cr
    @30
    @34
    @8
    @43
    wceq
    @37
    @7
    mblvol
    syl
    #
    @24
    @8
    cr
    wcel
    #
    @29
    wph
    @21
    @23
    @48
    itg1climres.4
    @5
    @2
    cF
    i1fima2sn
    sylan
    #
    adantr
    eqeltrrd
    @14
    @7
    ovolsscl
    syl3anc
    eqeltrd
    #
    @25
    eqid
    #
    fmptd
    #
    @24
    vj
    cv
    #
    @25
    cfv
    #
    @53
    c1
    caddc
    co
    #
    @25
    cfv
    #
    cle
    wbr
    #
    vj
    cn
    @24
    @15
    @7
    @12
    c1
    caddc
    co
    #
    cA
    cfv
    #
    cin
    #
    cvol
    cfv
    #
    cle
    wbr
    #
    vn
    cn
    wral
    #
    @57
    vj
    cn
    wral
    #
    @24
    @62
    vn
    cn
    @30
    @31
    @60
    covol
    cfv
    #
    @15
    @61
    cle
    @30
    @14
    @60
    wss
    #
    @60
    cr
    wss
    #
    @31
    @65
    cle
    wbr
    @30
    @13
    @59
    wss
    #
    @66
    wph
    @29
    @68
    @23
    itg1climres.2
    adantlr
    @13
    @59
    @7
    sslin
    syl
    #
    @30
    @60
    @32
    wcel
    #
    @67
    @30
    @34
    @59
    @32
    wcel
    #
    @70
    @37
    @24
    cn
    @32
    cA
    wf
    #
    @58
    cn
    wcel
    @71
    @29
    wph
    @72
    @23
    itg1climres.1
    adantr
    @12
    peano2nn
    cn
    @32
    @58
    cA
    ffvelrn
    syl2an
    @7
    @59
    inmbl
    syl2anc
    #
    @60
    mblss
    syl
    @14
    @60
    ovolss
    syl2anc
    @40
    @30
    @70
    @61
    @65
    wceq
    @73
    @60
    mblvol
    syl
    3brtr4d
    ralrimiva
    @64
    @7
    @53
    cA
    cfv
    #
    cin
    #
    cvol
    cfv
    #
    @7
    @55
    cA
    cfv
    #
    cin
    #
    cvol
    cfv
    #
    cle
    wbr
    #
    vj
    cn
    wral
    @63
    @57
    @80
    vj
    cn
    @53
    cn
    wcel
    #
    @54
    @76
    @56
    @79
    cle
    vn
    @53
    @15
    @76
    cn
    @25
    @12
    @53
    wceq
    #
    @14
    @75
    cvol
    @82
    @13
    @74
    @7
    @12
    @53
    cA
    fveq2
    ineq2d
    #
    fveq2d
    #
    @51
    @75
    cvol
    fvex
    fvmpt
    #
    @81
    @55
    cn
    wcel
    #
    @56
    @79
    wceq
    @53
    peano2nn
    #
    vn
    @55
    @15
    @79
    cn
    @25
    @12
    @55
    wceq
    #
    @14
    @78
    cvol
    @88
    @13
    @77
    @7
    @12
    @55
    cA
    fveq2
    ineq2d
    #
    fveq2d
    @51
    @78
    cvol
    fvex
    fvmpt
    syl
    breq12d
    ralbiia
    @62
    @80
    vn
    vj
    cn
    @82
    @15
    @76
    @61
    @79
    cle
    @84
    @82
    @60
    @78
    cvol
    @82
    @59
    @77
    @7
    @82
    @58
    @55
    cA
    @12
    @53
    c1
    caddc
    oveq1
    fveq2d
    ineq2d
    #
    fveq2d
    breq12d
    cbvralv
    bitr4i
    sylibr
    r19.21bi
    @24
    @48
    @54
    @8
    cle
    wbr
    #
    vj
    cn
    wral
    #
    @54
    vx
    cv
    #
    cle
    wbr
    #
    vj
    cn
    wral
    #
    vx
    cr
    wrex
    #
    @49
    @24
    @15
    @8
    cle
    wbr
    #
    vn
    cn
    wral
    #
    @92
    @24
    @97
    vn
    cn
    @30
    @31
    @43
    @15
    @8
    cle
    @30
    @41
    @42
    @31
    @43
    cle
    wbr
    @44
    @46
    @14
    @7
    ovolss
    sylancr
    @40
    @47
    3brtr4d
    ralrimiva
    @92
    @76
    @8
    cle
    wbr
    #
    vj
    cn
    wral
    @98
    @91
    @99
    vj
    cn
    @81
    @54
    @76
    @8
    cle
    @85
    breq1d
    ralbiia
    @97
    @99
    vn
    vj
    cn
    @82
    @15
    @76
    @8
    cle
    @84
    breq1d
    cbvralv
    bitr4i
    sylibr
    @95
    @92
    vx
    @8
    cr
    @93
    @8
    wceq
    @94
    @91
    vj
    cn
    @93
    @8
    @54
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    #
    climsup
    @24
    vn
    cn
    @14
    cmpt
    #
    crn
    #
    cuni
    #
    cvol
    cfv
    #
    cvol
    @102
    cima
    #
    cxr
    clt
    csup
    #
    @8
    @28
    @24
    cn
    @32
    @101
    wf
    #
    @53
    @101
    cfv
    #
    @55
    @101
    cfv
    #
    wss
    #
    vj
    cn
    wral
    #
    @104
    @106
    wceq
    @24
    vn
    cn
    @14
    @32
    @101
    @39
    @101
    eqid
    #
    fmptd
    #
    @24
    @66
    vn
    cn
    wral
    #
    @111
    @24
    @66
    vn
    cn
    @69
    ralrimiva
    @111
    @75
    @78
    wss
    #
    vj
    cn
    wral
    @114
    @110
    @115
    vj
    cn
    @81
    @108
    @75
    @109
    @78
    vn
    @53
    @14
    @75
    cn
    @101
    @83
    @112
    @74
    @7
    @53
    cA
    fvex
    inex2
    fvmpt
    #
    @81
    @86
    @109
    @78
    wceq
    @87
    vn
    @55
    @14
    @78
    cn
    @101
    @89
    @112
    @77
    @7
    @55
    cA
    fvex
    inex2
    fvmpt
    syl
    sseq12d
    ralbiia
    @66
    @115
    vn
    vj
    cn
    @82
    @14
    @75
    @60
    @78
    @83
    @90
    sseq12d
    cbvralv
    bitr4i
    sylibr
    vj
    @101
    volsup
    syl2anc
    @24
    @7
    @103
    cvol
    @24
    vj
    cn
    @108
    ciun
    #
    @7
    @103
    @24
    @117
    @7
    vn
    cn
    @13
    ciun
    #
    cin
    #
    @7
    @117
    vj
    cn
    @75
    ciun
    vn
    cn
    @14
    ciun
    @119
    vj
    cn
    @108
    @75
    @116
    iuneq2i
    vn
    vj
    cn
    @14
    @75
    @83
    cbviunv
    vn
    cn
    @7
    @13
    iunin2
    3eqtr2i
    @24
    @119
    @7
    cr
    cin
    #
    @7
    @24
    @118
    cr
    @7
    wph
    @118
    cr
    wceq
    @23
    wph
    @118
    cA
    crn
    cuni
    #
    cr
    wph
    @72
    cA
    cn
    wfn
    @118
    @121
    wceq
    itg1climres.1
    cn
    @32
    cA
    ffn
    vn
    cn
    cA
    fniunfv
    3syl
    itg1climres.3
    eqtrd
    adantr
    ineq2d
    @24
    @42
    @120
    @7
    wceq
    @24
    @34
    @42
    wph
    @34
    @23
    @36
    adantr
    @45
    syl
    @7
    cr
    df-ss
    sylib
    eqtrd
    syl5eq
    @24
    @107
    @101
    cn
    wfn
    @117
    @103
    wceq
    @113
    cn
    @32
    @101
    ffn
    vj
    cn
    @101
    fniunfv
    3syl
    eqtr3d
    fveq2d
    @24
    @27
    cxr
    clt
    csup
    #
    @28
    @106
    @24
    @27
    cr
    wss
    #
    @27
    c0
    wne
    #
    vz
    cv
    #
    @93
    cle
    wbr
    #
    vz
    @27
    wral
    #
    vx
    cr
    wrex
    #
    @122
    @28
    wceq
    @24
    cn
    cr
    @25
    wf
    #
    @123
    @52
    cn
    cr
    @25
    frn
    syl
    @24
    @25
    cdm
    #
    c0
    wne
    @124
    @24
    @130
    cn
    c0
    @24
    @129
    @130
    cn
    wceq
    @52
    cn
    cr
    @25
    fdm
    syl
    c1
    cn
    wcel
    cn
    c0
    wne
    @24
    1nn
    cn
    c1
    ne0i
    mp1i
    eqnetrd
    @130
    c0
    @27
    c0
    @25
    dm0rn0
    necon3bii
    sylib
    @24
    @128
    @96
    @100
    @24
    @127
    @95
    vx
    cr
    @24
    @129
    @25
    cn
    wfn
    @127
    @95
    wb
    @52
    cn
    cr
    @25
    ffn
    @126
    @94
    vz
    vj
    cn
    @25
    @125
    @54
    @93
    cle
    breq1
    ralrn
    3syl
    rexbidv
    mpbird
    vx
    vz
    @27
    supxrre
    syl3anc
    @24
    cxr
    @27
    @105
    clt
    @24
    @105
    cvol
    @101
    ccom
    #
    crn
    @27
    cvol
    @101
    rnco2
    @24
    @131
    @25
    @24
    vn
    vy
    cn
    @32
    @14
    vy
    cv
    #
    cvol
    cfv
    @15
    @101
    cvol
    @39
    @24
    @101
    eqidd
    @24
    vy
    @32
    cc0
    cpnf
    cicc
    co
    #
    cvol
    @32
    @133
    cvol
    wf
    @24
    volf
    a1i
    feqmptd
    @132
    @14
    cvol
    fveq2
    fmptco
    rneqd
    syl5reqr
    supeq1d
    eqtr3d
    3eqtr4d
    breqtrrd
    @24
    @5
    wph
    @4
    cr
    @5
    wph
    @2
    cr
    @3
    wph
    @21
    cr
    cr
    cF
    wf
    #
    @2
    cr
    wss
    #
    itg1climres.4
    cF
    i1ff
    #
    cr
    cr
    cF
    frn
    3syl
    #
    ssdifssd
    sselda
    #
    recnd
    @17
    cvv
    wcel
    @24
    vn
    cn
    @16
    nnex
    mptex
    a1i
    @24
    @81
    wa
    #
    @54
    @24
    cn
    cr
    @53
    @25
    @52
    ffvelrnda
    recnd
    @81
    @53
    @17
    cfv
    #
    @5
    @54
    cmul
    co
    #
    wceq
    @24
    @81
    @140
    @5
    @76
    cmul
    co
    #
    @141
    vn
    @53
    @16
    @142
    cn
    @17
    @82
    @15
    @76
    @5
    cmul
    @84
    oveq2d
    #
    @17
    eqid
    #
    @5
    @76
    cmul
    ovex
    fvmpt
    #
    @81
    @54
    @76
    @5
    cmul
    @85
    oveq2d
    eqtr4d
    adantl
    climmulc2
    @1
    cvv
    wcel
    wph
    vn
    cn
    @0
    nnex
    mptex
    a1i
    wph
    @23
    @81
    @140
    cc
    wcel
    @139
    @140
    @24
    cn
    cr
    @53
    @17
    @24
    vn
    cn
    @16
    cr
    @17
    @30
    @5
    @15
    @24
    @5
    cr
    wcel
    @29
    @138
    adantr
    @50
    remulcld
    @144
    fmptd
    ffvelrnda
    recnd
    anasss
    wph
    @81
    @53
    @1
    cfv
    @53
    vn
    cn
    @4
    @16
    vk
    csu
    #
    cmpt
    #
    cfv
    #
    @4
    @140
    vk
    csu
    #
    wph
    @53
    @1
    @147
    wph
    vn
    cn
    @0
    @146
    wph
    @29
    wa
    #
    @0
    @4
    @5
    cG
    ccnv
    #
    @6
    cima
    #
    cvol
    cfv
    #
    cmul
    co
    #
    vk
    csu
    #
    @146
    @150
    cG
    @20
    wcel
    #
    @19
    cG
    crn
    #
    @3
    cdif
    @4
    wss
    #
    @4
    cr
    @3
    cdif
    wss
    @0
    @155
    wceq
    @150
    @21
    @35
    @156
    wph
    @21
    @29
    itg1climres.4
    adantr
    @38
    vx
    @13
    cF
    cG
    itg1climres.5
    i1fres
    syl2anc
    #
    wph
    @19
    @29
    @22
    adantr
    @150
    cr
    @2
    cG
    wf
    @157
    @2
    wss
    @158
    @150
    vx
    cr
    @93
    @13
    wcel
    #
    @93
    cF
    cfv
    #
    cc0
    cif
    #
    @2
    cG
    @150
    @93
    cr
    wcel
    #
    wa
    @160
    @161
    cc0
    @2
    @150
    cF
    cr
    wfn
    #
    @163
    @161
    @2
    wcel
    wph
    @164
    @29
    wph
    @21
    @134
    @164
    itg1climres.4
    @136
    cr
    cr
    cF
    ffn
    3syl
    adantr
    #
    cr
    @93
    cF
    fnfvelrn
    sylan
    wph
    cc0
    @2
    wcel
    #
    @29
    @163
    wph
    @21
    @166
    itg1climres.4
    cF
    i1f0rn
    syl
    ad2antrr
    ifcld
    itg1climres.5
    fmptd
    cr
    @2
    cG
    frn
    @157
    @2
    @3
    ssdif
    3syl
    @150
    @2
    cr
    @3
    wph
    @135
    @29
    @137
    adantr
    ssdifd
    vk
    @4
    cG
    itg1val2
    syl13anc
    @150
    @4
    @154
    @16
    vk
    @150
    @23
    wa
    #
    @153
    @15
    @5
    cmul
    @167
    @152
    @14
    cvol
    @167
    @93
    @152
    wcel
    #
    @93
    @14
    wcel
    #
    wb
    #
    vx
    wal
    @152
    @14
    wceq
    @167
    @170
    vx
    @167
    @163
    @93
    cG
    cfv
    #
    @5
    wceq
    #
    wa
    #
    @163
    @161
    @5
    wceq
    #
    wa
    #
    @160
    wa
    #
    @168
    @169
    @167
    @173
    @163
    @174
    @160
    wa
    #
    wa
    @176
    @167
    @163
    @172
    @177
    @167
    @163
    wa
    #
    @172
    @160
    @162
    @5
    wceq
    #
    wa
    #
    @177
    @178
    @172
    @179
    @180
    @178
    @171
    @162
    @5
    @163
    @171
    @162
    wceq
    #
    @167
    @163
    @162
    cvv
    wcel
    @181
    @160
    @161
    cc0
    @93
    cF
    fvex
    c0ex
    ifex
    vx
    cr
    @162
    cvv
    cG
    itg1climres.5
    fvmpt2
    mpan2
    adantl
    eqeq1d
    @178
    @179
    @160
    @178
    @179
    @162
    cc0
    wne
    #
    @160
    @178
    @182
    @179
    @5
    cc0
    wne
    #
    @23
    @183
    @150
    @163
    @5
    @2
    cc0
    eldifsni
    ad2antlr
    @162
    @5
    cc0
    neeq1
    syl5ibrcom
    @160
    @162
    cc0
    @160
    @161
    cc0
    iffalse
    necon1ai
    syl6
    pm4.71rd
    bitrd
    @180
    @160
    @174
    wa
    @177
    @160
    @179
    @174
    @160
    @162
    @161
    @5
    @160
    @161
    cc0
    iftrue
    eqeq1d
    pm5.32i
    @160
    @174
    ancom
    bitri
    syl6bb
    pm5.32da
    @163
    @174
    @160
    anass
    syl6bbr
    @167
    cG
    cr
    wfn
    #
    @168
    @173
    wb
    @150
    @184
    @23
    @150
    @156
    cr
    cr
    cG
    wf
    @184
    @159
    cG
    i1ff
    cr
    cr
    cG
    ffn
    3syl
    adantr
    cr
    @5
    @93
    cG
    fniniseg
    syl
    @169
    @93
    @7
    wcel
    #
    @160
    wa
    @167
    @176
    @93
    @7
    @13
    elin
    @167
    @185
    @175
    @160
    @167
    @164
    @185
    @175
    wb
    @150
    @164
    @23
    @165
    adantr
    cr
    @5
    @93
    cF
    fniniseg
    syl
    anbi1d
    syl5bb
    3bitr4d
    alrimiv
    vx
    @152
    @14
    vx
    @151
    @6
    vx
    cG
    vx
    cG
    vx
    cr
    @162
    cmpt
    itg1climres.5
    vx
    cr
    @162
    nfmpt1
    nfcxfr
    nfcnv
    vx
    @6
    nfcv
    nfima
    vx
    @14
    nfcv
    cleqf
    sylibr
    fveq2d
    oveq2d
    sumeq2dv
    eqtrd
    mpteq2dva
    fveq1d
    @81
    @148
    @4
    @142
    vk
    csu
    #
    @149
    vn
    @53
    @146
    @186
    cn
    @147
    @82
    @4
    @16
    @142
    vk
    @143
    sumeq2sdv
    @147
    eqid
    @4
    @142
    vk
    sumex
    fvmpt
    @81
    @4
    @140
    @142
    vk
    @145
    sumeq2sdv
    eqtr4d
    sylan9eq
    climfsum
    wph
    @21
    @11
    @10
    wceq
    itg1climres.4
    vk
    cF
    itg1val
    syl
    breqtrrd
end
