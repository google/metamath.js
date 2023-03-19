include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "csu.mm"
include "cabs.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cfa.mm"
include "cmul.mm"
include "cdiv.mm"
include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "eftlcl.mm"
include "syl2anc.mm"
include "abscld.mm"
include "cr.mm"
include "reeftlcl.mm"
include "reexpcld.mm"
include "peano2nn0.mm"
include "syl.mm"
include "nn0red.mm"
include "cn.mm"
include "faccl.mm"
include "nnmulcld.mm"
include "nndivred.mm"
include "remulcld.mm"
include "eqid.mm"
include "nnzd.mm"
include "wa.mm"
include "eqidd.mm"
include "eluznn0.mm"
include "sylan.mm"
include "wceq.mm"
include "eftval.mm"
include "adantl.mm"
include "eftcl.mm"
include "eqeltrd.mm"
include "syldan.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "eftlcvg.mm"
include "isumclim2.mm"
include "reeftcl.mm"
include "recnd.mm"
include "eftabs.mm"
include "fveq2d.mm"
include "3eqtr4rd.mm"
include "iserabs.mm"
include "cle.mm"
include "cneg.mm"
include "cshi.mm"
include "cc0.mm"
include "nn0uz.mm"
include "0zd.mm"
include "nncnd.mm"
include "nn0cn.mm"
include "cmpt.mm"
include "cvv.mm"
include "nn0ex.mm"
include "mptex.mm"
include "eqeltri.mm"
include "shftval4.mm"
include "syl2an.mm"
include "nn0addcl.mm"
include "adantr.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "peano2nnd.mm"
include "nnrecred.mm"
include "reexpcl.mm"
include "wbr.mm"
include "nnred.mm"
include "cz.mm"
include "uzid.mm"
include "uzaddcl.mm"
include "absge0d.mm"
include "leexp2rd.mm"
include "nnexpcl.mm"
include "expge0d.mm"
include "jca.mm"
include "faclbnd6.mm"
include "lemul1a.mm"
include "syl31anc.mm"
include "nnrpd.mm"
include "lemuldiv2d.mm"
include "mpbid.mm"
include "nnne0d.mm"
include "divassd.mm"
include "nn0z.mm"
include "exprecd.mm"
include "divrecd.mm"
include "wne.mm"
include "facne0.mm"
include "divdiv1d.mm"
include "3eqtr2rd.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "letrd.mm"
include "clt.mm"
include "wb.mm"
include "nngt0d.mm"
include "ledivmul.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "eqbrtrd.mm"
include "cmin.mm"
include "0z.mm"
include "znegcld.mm"
include "seqshft.mm"
include "sylancr.mm"
include "0cn.mm"
include "subneg.mm"
include "mpan.mm"
include "addid2.mm"
include "seqeq1d.mm"
include "seqex.mm"
include "climshft.mm"
include "sylancl.mm"
include "sumex.mm"
include "breldm.mm"
include "nnge1d.mm"
include "1nn.mm"
include "nnleltp1.mm"
include "nn0ge0d.mm"
include "absidd.mm"
include "breqtrrd.mm"
include "georeclim.mm"
include "eqtr4d.mm"
include "isermulc2.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "div23d.mm"
include "mulcomd.mm"
include "3eqtrd.mm"
include "isumle.mm"
include "fveq2.mm"
include "addid2d.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "isumshft.mm"
include "sumeq1d.mm"
include "eqtr3d.mm"
include "isumclim.mm"
include "3brtr3d.mm"

theorem eftlub
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let vj: setvar j
  assume eftl.1: |- F = ( n e. NN0 |-> ( ( A ^ n ) / ( ! ` n ) ) )
  assume eftl.2: |- G = ( n e. NN0 |-> ( ( ( abs ` A ) ^ n ) / ( ! ` n ) ) )
  assume eftl.3: |- H = ( n e. NN0 |-> ( ( ( ( abs ` A ) ^ M ) / ( ! ` M ) ) x. ( ( 1 / ( M + 1 ) ) ^ n ) ) )
  assume eftl.4: |- ( ph -> M e. NN )
  assume eftl.5: |- ( ph -> A e. CC )
  assume eftl.6: |- ( ph -> ( abs ` A ) <_ 1 )

  disjoint k n
  disjoint A k
  disjoint A n
  disjoint F k
  disjoint G k
  disjoint M k
  disjoint M n
  disjoint k ph
  disjoint j k
  disjoint j n
  disjoint A j
  disjoint G j
  disjoint H j
  disjoint M j
  disjoint j ph
  assert |- ( ph -> ( abs ` sum_ k e. ( ZZ>= ` M ) ( F ` k ) ) <_ ( ( ( abs ` A ) ^ M ) x. ( ( M + 1 ) / ( ( ! ` M ) x. M ) ) ) )

  proof
    wph
    cM
    cuz
    cfv
    #
    vk
    cv
    #
    cF
    cfv
    #
    vk
    csu
    #
    cabs
    cfv
    @0
    @1
    cG
    cfv
    #
    vk
    csu
    #
    cA
    cabs
    cfv
    #
    cM
    cexp
    co
    #
    cM
    c1
    caddc
    co
    #
    cM
    cfa
    cfv
    #
    cM
    cmul
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    wph
    @3
    wph
    cA
    cc
    wcel
    #
    cM
    cn0
    wcel
    #
    @3
    cc
    wcel
    eftl.5
    wph
    cM
    eftl.4
    nnnn0d
    #
    cA
    vk
    vn
    cF
    cM
    eftl.1
    eftlcl
    syl2anc
    abscld
    wph
    @6
    cr
    wcel
    #
    @14
    @5
    cr
    wcel
    wph
    cA
    eftl.5
    abscld
    #
    @15
    @6
    vk
    vn
    cG
    cM
    eftl.2
    reeftlcl
    syl2anc
    wph
    @7
    @11
    wph
    @6
    cM
    @17
    @15
    reexpcld
    #
    wph
    @8
    @10
    wph
    @8
    wph
    @14
    @8
    cn0
    wcel
    @15
    cM
    peano2nn0
    syl
    #
    nn0red
    #
    wph
    @9
    cM
    wph
    @14
    @9
    cn
    wcel
    #
    @15
    cM
    faccl
    syl
    #
    eftl.4
    nnmulcld
    nndivred
    remulcld
    wph
    @3
    @5
    vk
    cF
    cG
    cM
    @0
    @0
    eqid
    #
    wph
    @2
    vk
    cF
    cM
    @0
    @23
    wph
    cM
    eftl.4
    nnzd
    #
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @2
    eqidd
    wph
    @25
    @1
    cn0
    wcel
    #
    @2
    cc
    wcel
    wph
    @14
    @25
    @27
    @15
    @1
    cM
    eluznn0
    sylan
    #
    wph
    @27
    wa
    #
    @2
    cA
    @1
    cexp
    co
    @1
    cfa
    cfv
    #
    cdiv
    co
    #
    cc
    @27
    @2
    @31
    wceq
    wph
    cA
    vn
    cF
    @1
    eftl.1
    eftval
    adantl
    #
    wph
    @13
    @27
    @31
    cc
    wcel
    eftl.5
    cA
    @1
    eftcl
    sylan
    eqeltrd
    syldan
    #
    wph
    @13
    @14
    caddc
    cF
    cM
    cseq
    cli
    cdm
    #
    wcel
    eftl.5
    @15
    cA
    vn
    cF
    cM
    eftl.1
    eftlcvg
    syl2anc
    isumclim2
    wph
    @4
    vk
    cG
    cM
    @0
    @23
    @24
    @26
    @4
    eqidd
    @26
    @4
    wph
    @25
    @27
    @4
    cr
    wcel
    @28
    @29
    @4
    @6
    @1
    cexp
    co
    @30
    cdiv
    co
    #
    cr
    @27
    @4
    @35
    wceq
    wph
    @6
    vn
    cG
    @1
    eftl.2
    eftval
    adantl
    #
    wph
    @16
    @27
    @35
    cr
    wcel
    @17
    @6
    @1
    reeftcl
    sylan
    eqeltrd
    syldan
    recnd
    #
    wph
    @6
    cc
    wcel
    @14
    caddc
    cG
    cM
    cseq
    #
    @34
    wcel
    wph
    @6
    @17
    recnd
    @15
    @6
    vn
    cG
    cM
    eftl.2
    eftlcvg
    syl2anc
    isumclim2
    #
    @24
    @33
    wph
    @25
    @27
    @4
    @2
    cabs
    cfv
    #
    wceq
    @28
    @29
    @31
    cabs
    cfv
    #
    @35
    @40
    @4
    wph
    @13
    @27
    @41
    @35
    wceq
    eftl.5
    cA
    @1
    eftabs
    sylan
    @29
    @2
    @31
    cabs
    @32
    fveq2d
    @36
    3eqtr4rd
    syldan
    iserabs
    wph
    cn0
    cM
    vj
    cv
    #
    caddc
    co
    #
    cG
    cfv
    #
    vj
    csu
    #
    cn0
    @7
    @9
    cdiv
    co
    #
    c1
    @8
    cdiv
    co
    #
    @42
    cexp
    co
    #
    cmul
    co
    #
    vj
    csu
    @5
    @12
    cle
    wph
    @44
    @49
    vj
    cG
    cM
    cneg
    #
    cshi
    co
    #
    cH
    cc0
    cn0
    nn0uz
    wph
    0zd
    #
    wph
    cM
    cc
    wcel
    #
    @42
    cc
    wcel
    @42
    @51
    cfv
    @44
    wceq
    @42
    cn0
    wcel
    #
    wph
    cM
    eftl.4
    nncnd
    #
    @42
    nn0cn
    cM
    @42
    cG
    cG
    vn
    cn0
    @6
    vn
    cv
    #
    cexp
    co
    @56
    cfa
    cfv
    cdiv
    co
    #
    cmpt
    cvv
    eftl.2
    vn
    cn0
    @57
    nn0ex
    mptex
    eqeltri
    #
    shftval4
    syl2an
    wph
    @54
    wa
    #
    @44
    @6
    @43
    cexp
    co
    #
    @43
    cfa
    cfv
    #
    cdiv
    co
    #
    cr
    @59
    @43
    cn0
    wcel
    #
    @44
    @62
    wceq
    wph
    @14
    @54
    @63
    @15
    cM
    @42
    nn0addcl
    sylan
    #
    @6
    vn
    cG
    @43
    eftl.2
    eftval
    syl
    #
    @59
    @16
    @63
    @62
    cr
    wcel
    wph
    @16
    @54
    @17
    adantr
    #
    @64
    @6
    @43
    reeftcl
    syl2anc
    eqeltrd
    @54
    @42
    cH
    cfv
    #
    @49
    wceq
    wph
    vn
    @42
    @46
    @47
    @56
    cexp
    co
    #
    cmul
    co
    @49
    cn0
    cH
    @56
    @42
    wceq
    @68
    @48
    @46
    cmul
    @56
    @42
    @47
    cexp
    oveq2
    #
    oveq2d
    eftl.3
    @46
    @48
    cmul
    ovex
    fvmpt
    adantl
    #
    @59
    @46
    @48
    wph
    @46
    cr
    wcel
    @54
    wph
    @7
    @9
    @18
    @22
    nndivred
    #
    adantr
    wph
    @47
    cr
    wcel
    @54
    @48
    cr
    wcel
    wph
    @8
    wph
    cM
    eftl.4
    peano2nnd
    #
    nnrecred
    @47
    @42
    reexpcl
    sylan
    #
    remulcld
    #
    @59
    @44
    @62
    @49
    cle
    @65
    @59
    @62
    @49
    cle
    wbr
    #
    @60
    @61
    @49
    cmul
    co
    #
    cle
    wbr
    #
    @59
    @60
    @7
    @76
    @59
    @6
    @43
    @66
    @64
    reexpcld
    #
    wph
    @7
    cr
    wcel
    #
    @54
    @18
    adantr
    #
    @59
    @61
    @49
    @59
    @61
    @59
    @63
    @61
    cn
    wcel
    @64
    @43
    faccl
    syl
    #
    nnred
    #
    @74
    remulcld
    @59
    @6
    cM
    @43
    @66
    wph
    @14
    @54
    @15
    adantr
    wph
    cM
    @0
    wcel
    #
    @54
    @43
    @0
    wcel
    wph
    cM
    cz
    wcel
    @83
    @24
    cM
    uzid
    syl
    @42
    cM
    cM
    uzaddcl
    sylan
    wph
    cc0
    @6
    cle
    wbr
    @54
    wph
    cA
    eftl.5
    absge0d
    #
    adantr
    wph
    @6
    c1
    cle
    wbr
    @54
    eftl.6
    adantr
    leexp2rd
    @59
    @7
    @61
    @7
    cmul
    co
    #
    @9
    @8
    @42
    cexp
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    @76
    cle
    @59
    @87
    @7
    cmul
    co
    @85
    cle
    wbr
    #
    @7
    @88
    cle
    wbr
    @59
    @87
    cr
    wcel
    @61
    cr
    wcel
    #
    @79
    cc0
    @7
    cle
    wbr
    #
    wa
    #
    @87
    @61
    cle
    wbr
    #
    @89
    @59
    @87
    @59
    @9
    @86
    wph
    @21
    @54
    @22
    adantr
    wph
    @8
    cn
    wcel
    #
    @54
    @86
    cn
    wcel
    @72
    @8
    @42
    nnexpcl
    sylan
    #
    nnmulcld
    #
    nnred
    @82
    wph
    @92
    @54
    wph
    @79
    @91
    @18
    wph
    @6
    cM
    @17
    @15
    @84
    expge0d
    jca
    adantr
    wph
    @14
    @54
    @93
    @15
    @42
    cM
    faclbnd6
    sylan
    @87
    @61
    @7
    lemul1a
    syl31anc
    @59
    @7
    @85
    @87
    @80
    @59
    @61
    @7
    @82
    @80
    remulcld
    @59
    @87
    @96
    nnrpd
    lemuldiv2d
    mpbid
    @59
    @88
    @61
    @7
    @87
    cdiv
    co
    #
    cmul
    co
    @76
    @59
    @61
    @7
    @87
    @59
    @61
    @81
    nncnd
    wph
    @7
    cc
    wcel
    @54
    wph
    @7
    @18
    recnd
    #
    adantr
    #
    @59
    @87
    @96
    nncnd
    @59
    @87
    @96
    nnne0d
    divassd
    @59
    @97
    @49
    @61
    cmul
    @59
    @49
    @46
    c1
    @86
    cdiv
    co
    #
    cmul
    co
    @46
    @86
    cdiv
    co
    @97
    @59
    @48
    @100
    @46
    cmul
    @59
    @8
    @42
    wph
    @8
    cc
    wcel
    @54
    wph
    @8
    @72
    nncnd
    #
    adantr
    @59
    @8
    wph
    @94
    @54
    @72
    adantr
    nnne0d
    @54
    @42
    cz
    wcel
    wph
    @42
    nn0z
    adantl
    exprecd
    oveq2d
    @59
    @46
    @86
    wph
    @46
    cc
    wcel
    @54
    wph
    @46
    @71
    recnd
    #
    adantr
    @59
    @86
    @95
    nncnd
    #
    @59
    @86
    @95
    nnne0d
    #
    divrecd
    @59
    @7
    @9
    @86
    @99
    wph
    @9
    cc
    wcel
    @54
    wph
    @9
    @22
    nncnd
    #
    adantr
    @103
    wph
    @9
    cc0
    wne
    #
    @54
    wph
    @14
    @106
    @15
    cM
    facne0
    syl
    #
    adantr
    @104
    divdiv1d
    3eqtr2rd
    oveq2d
    eqtrd
    breqtrd
    letrd
    @59
    @60
    cr
    wcel
    @49
    cr
    wcel
    @90
    cc0
    @61
    clt
    wbr
    @75
    @77
    wb
    @78
    @74
    @82
    @59
    @61
    @81
    nngt0d
    @60
    @49
    @61
    ledivmul
    syl112anc
    mpbird
    eqbrtrd
    wph
    caddc
    @51
    cc0
    cseq
    #
    caddc
    cG
    cc0
    @50
    cmin
    co
    #
    cseq
    #
    @50
    cshi
    co
    #
    @34
    wph
    cc0
    cz
    wcel
    @50
    cz
    wcel
    #
    @108
    @111
    wceq
    0z
    wph
    cM
    @24
    znegcld
    #
    caddc
    cG
    cc0
    @50
    @58
    seqshft
    sylancr
    wph
    @111
    @5
    cli
    wbr
    #
    @111
    @34
    wcel
    wph
    @114
    @110
    @5
    cli
    wbr
    #
    wph
    @110
    @38
    @5
    cli
    wph
    @109
    cM
    caddc
    cG
    wph
    @53
    @109
    cM
    wceq
    @55
    @53
    @109
    cc0
    cM
    caddc
    co
    #
    cM
    cc0
    cc
    wcel
    @53
    @109
    @116
    wceq
    0cn
    cc0
    cM
    subneg
    mpan
    cM
    addid2
    eqtrd
    syl
    seqeq1d
    @39
    eqbrtrd
    wph
    @112
    @110
    cvv
    wcel
    @114
    @115
    wb
    @113
    caddc
    cG
    @109
    seqex
    @5
    @110
    @50
    cvv
    climshft
    sylancl
    mpbird
    @111
    @5
    cli
    @110
    @50
    cshi
    ovex
    @0
    @4
    vk
    sumex
    breldm
    syl
    eqeltrd
    wph
    caddc
    cH
    cc0
    cseq
    #
    @12
    cli
    wbr
    @117
    @34
    wcel
    wph
    @117
    @46
    @8
    @8
    c1
    cmin
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    @12
    cli
    wph
    @119
    @46
    vj
    vn
    cn0
    @68
    cmpt
    #
    cH
    cc0
    cn0
    nn0uz
    @52
    @102
    wph
    @8
    vj
    @121
    @101
    wph
    c1
    @8
    @8
    cabs
    cfv
    clt
    wph
    c1
    cM
    cle
    wbr
    #
    c1
    @8
    clt
    wbr
    #
    wph
    cM
    eftl.4
    nnge1d
    wph
    c1
    cn
    wcel
    cM
    cn
    wcel
    @122
    @123
    wb
    1nn
    eftl.4
    c1
    cM
    nnleltp1
    sylancr
    mpbid
    wph
    @8
    @20
    wph
    @8
    @19
    nn0ge0d
    absidd
    breqtrrd
    @54
    @42
    @121
    cfv
    #
    @48
    wceq
    wph
    vn
    @42
    @68
    @48
    cn0
    @121
    @69
    @121
    eqid
    @47
    @42
    cexp
    ovex
    fvmpt
    adantl
    #
    georeclim
    @59
    @124
    @48
    cc
    @125
    @59
    @48
    @73
    recnd
    eqeltrd
    @59
    @67
    @49
    @46
    @124
    cmul
    co
    @70
    @59
    @124
    @48
    @46
    cmul
    @125
    oveq2d
    eqtr4d
    isermulc2
    wph
    @120
    @7
    @8
    cM
    cdiv
    co
    #
    cmul
    co
    @9
    cdiv
    co
    #
    @7
    @126
    @9
    cdiv
    co
    #
    cmul
    co
    @12
    wph
    @120
    @46
    @126
    cmul
    co
    @127
    wph
    @119
    @126
    @46
    cmul
    wph
    @118
    cM
    @8
    cdiv
    wph
    @53
    c1
    cc
    wcel
    @118
    cM
    wceq
    @55
    ax-1cn
    cM
    c1
    pncan
    sylancl
    oveq2d
    oveq2d
    wph
    @7
    @126
    @9
    @98
    wph
    @126
    wph
    @8
    cM
    @20
    eftl.4
    nndivred
    recnd
    #
    @105
    @107
    div23d
    eqtr4d
    wph
    @7
    @126
    @9
    @98
    @129
    @105
    @107
    divassd
    wph
    @128
    @11
    @7
    cmul
    wph
    @128
    @8
    cM
    @9
    cmul
    co
    #
    cdiv
    co
    @11
    wph
    @8
    cM
    @9
    @101
    @55
    @105
    wph
    cM
    eftl.4
    nnne0d
    @107
    divdiv1d
    wph
    @130
    @10
    @8
    cdiv
    wph
    cM
    @9
    @55
    @105
    mulcomd
    oveq2d
    eqtrd
    oveq2d
    3eqtrd
    breqtrd
    #
    @117
    @12
    cli
    caddc
    cH
    cc0
    seqex
    @7
    @11
    cmul
    ovex
    breldm
    syl
    isumle
    wph
    @116
    cuz
    cfv
    #
    @4
    vk
    csu
    @45
    @5
    wph
    @4
    @44
    vk
    vj
    cM
    cc0
    @132
    cn0
    nn0uz
    @132
    eqid
    @1
    @43
    cG
    fveq2
    @24
    @52
    wph
    @1
    @132
    wcel
    #
    @25
    @4
    cc
    wcel
    wph
    @133
    @25
    wph
    @132
    @0
    @1
    wph
    @116
    cM
    cuz
    wph
    cM
    @55
    addid2d
    fveq2d
    #
    eleq2d
    biimpa
    @37
    syldan
    isumshft
    wph
    @132
    @0
    @4
    vk
    @134
    sumeq1d
    eqtr3d
    wph
    @49
    @12
    vj
    cH
    cc0
    cn0
    nn0uz
    @52
    @70
    @59
    @49
    @74
    recnd
    @131
    isumclim
    3brtr3d
    letrd
end
