include "cc.mm"
include "cdv.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cfv.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "wceq.mm"
include "c1.mm"
include "cmin.mm"
include "cif.mm"
include "oveq2d.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "ctop.mm"
include "wcel.mm"
include "eqid.mm"
include "cnfldtop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cr.mm"
include "cpr.mm"
include "cnelprrecn.mm"
include "a1i.mm"
include "topopn.mm"
include "mp1i.mm"
include "fzfid.mm"
include "wa.mm"
include "cn0.mm"
include "wf.mm"
include "elfznn0.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "adantr.mm"
include "simpr.mm"
include "ad2antlr.mm"
include "expcld.mm"
include "mulcld.mm"
include "3impa.mm"
include "w3a.mm"
include "3adant3.mm"
include "0cnd.mm"
include "wn.mm"
include "simpl2.mm"
include "syl.mm"
include "nn0cnd.mm"
include "simpl3.mm"
include "cn.mm"
include "wo.mm"
include "elnn0.mm"
include "sylib.mm"
include "orel2.mm"
include "sylc.mm"
include "nnm1nn0.mm"
include "ifclda.mm"
include "cvv.mm"
include "c0ex.mm"
include "ovex.mm"
include "ifex.mm"
include "adantl.mm"
include "dvexp2.mm"
include "dvmptcmul.mm"
include "dvmptfsum.mm"
include "elfznn.mm"
include "nnne0d.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "sumeq2dv.mm"
include "cuz.mm"
include "wss.mm"
include "1eluzge0.mm"
include "fzss1.mm"
include "nnnn0d.mm"
include "wne.mm"
include "simplr.mm"
include "eqeltrd.mm"
include "cdif.mm"
include "caddc.mm"
include "eldifn.mm"
include "0p1e1.mm"
include "oveq1i.mm"
include "eleq2i.mm"
include "sylnibr.mm"
include "eldifi.mm"
include "wb.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "ad2antrr.mm"
include "elfzp12.mm"
include "mpbid.mm"
include "iftrued.mm"
include "mul01d.mm"
include "sylan2.mm"
include "eqtrd.mm"
include "fsumss.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "peano2nn0.mm"
include "ffvelrnd.mm"
include "mulassd.mm"
include "mulcomd.mm"
include "oveq1d.mm"
include "3eqtr2d.mm"
include "1m1e0.mm"
include "sumeq1i.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "oveq2.mm"
include "cbvsumv.mm"
include "3eqtr4g.mm"
include "1zzd.mm"
include "nn0zd.mm"
include "fveq2.mm"
include "id.mm"
include "fsumshftm.mm"
include "fvmpt2.mm"
include "3eqtr4d.mm"
include "3eqtr3d.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"

theorem dvply1
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cN: class N
  let vj: setvar j
  assume dvply1.f: |- ( ph -> F = ( z e. CC |-> sum_ k e. ( 0 ... N ) ( ( A ` k ) x. ( z ^ k ) ) ) )
  assume dvply1.g: |- ( ph -> G = ( z e. CC |-> sum_ k e. ( 0 ... ( N - 1 ) ) ( ( B ` k ) x. ( z ^ k ) ) ) )
  assume dvply1.a: |- ( ph -> A : NN0 --> CC )
  assume dvply1.b: |- B = ( k e. NN0 |-> ( ( k + 1 ) x. ( A ` ( k + 1 ) ) ) )
  assume dvply1.n: |- ( ph -> N e. NN0 )

  disjoint ph z
  disjoint k ph
  disjoint k z
  disjoint A z
  disjoint A k
  disjoint B z
  disjoint N k
  disjoint N z
  disjoint j ph
  disjoint j z
  disjoint j k
  disjoint A j
  disjoint N j
  assert |- ( ph -> ( CC _D F ) = G )

  proof
    wph
    cc
    cF
    cdv
    co
    cc
    vz
    cc
    cc0
    cN
    cfz
    co
    #
    vk
    cv
    #
    cA
    cfv
    #
    vz
    cv
    #
    @1
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    cmpt
    #
    cdv
    co
    vz
    cc
    @0
    @2
    @1
    cc0
    wceq
    #
    cc0
    @1
    @3
    @1
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    cG
    wph
    cF
    @6
    cc
    cdv
    dvply1.f
    oveq2d
    wph
    vz
    @5
    @12
    cc
    vk
    @0
    ccnfld
    ctopn
    cfv
    #
    @15
    cc
    @15
    cc
    crest
    co
    #
    @15
    @15
    ctop
    wcel
    #
    @16
    @15
    wceq
    @15
    @15
    eqid
    #
    cnfldtop
    #
    @15
    ctop
    cc
    cc
    @15
    @15
    @18
    cnfldtopon
    toponunii
    #
    restid
    ax-mp
    eqcomi
    @18
    cc
    cr
    cc
    cpr
    wcel
    #
    wph
    cnelprrecn
    a1i
    @17
    cc
    @15
    wcel
    wph
    @19
    @15
    cc
    @20
    topopn
    mp1i
    wph
    cc0
    cN
    fzfid
    wph
    @1
    @0
    wcel
    #
    @3
    cc
    wcel
    #
    @5
    cc
    wcel
    wph
    @22
    wa
    #
    @23
    wa
    #
    @2
    @4
    @24
    @2
    cc
    wcel
    #
    @23
    wph
    cn0
    cc
    cA
    wf
    #
    @1
    cn0
    wcel
    #
    @26
    @22
    dvply1.a
    @1
    cN
    elfznn0
    #
    cn0
    cc
    @1
    cA
    ffvelrn
    #
    syl2an
    #
    adantr
    @25
    @3
    @1
    @24
    @23
    simpr
    @22
    @28
    wph
    @23
    @29
    ad2antlr
    expcld
    #
    mulcld
    3impa
    wph
    @22
    @23
    w3a
    #
    @2
    @11
    wph
    @22
    @26
    @23
    @31
    3adant3
    @33
    @7
    cc0
    @10
    cc
    @33
    @7
    wa
    0cnd
    @33
    @7
    wn
    #
    wa
    #
    @1
    @9
    @35
    @1
    @35
    @22
    @28
    wph
    @22
    @23
    @34
    simpl2
    @29
    syl
    #
    nn0cnd
    @35
    @3
    @8
    wph
    @22
    @23
    @34
    simpl3
    @35
    @1
    cn
    wcel
    #
    @8
    cn0
    wcel
    #
    @35
    @34
    @37
    @7
    wo
    #
    @37
    @33
    @34
    simpr
    @35
    @28
    @39
    @36
    @1
    elnn0
    sylib
    @7
    @37
    orel2
    sylc
    @1
    nnm1nn0
    #
    syl
    expcld
    mulcld
    ifclda
    mulcld
    @24
    vz
    @4
    @11
    @2
    cc
    cvv
    cc
    @21
    @24
    cnelprrecn
    a1i
    @32
    @11
    cvv
    wcel
    @25
    @7
    cc0
    @10
    c0ex
    @1
    @9
    cmul
    ovex
    ifex
    a1i
    @24
    @28
    cc
    vz
    cc
    @4
    cmpt
    cdv
    co
    vz
    cc
    @11
    cmpt
    wceq
    @22
    @28
    wph
    @29
    adantl
    vz
    @1
    dvexp2
    syl
    @31
    dvmptcmul
    dvmptfsum
    wph
    @14
    vz
    cc
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    @1
    cB
    cfv
    #
    @4
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    cG
    wph
    vz
    cc
    @13
    @45
    wph
    @23
    wa
    #
    c1
    cN
    cfz
    co
    #
    @12
    vk
    csu
    @47
    @2
    @10
    cmul
    co
    #
    vk
    csu
    #
    @13
    @45
    @46
    @47
    @12
    @48
    vk
    @46
    @1
    @47
    wcel
    #
    wa
    #
    @11
    @10
    @2
    cmul
    @51
    @7
    cc0
    @10
    @50
    @34
    @46
    @50
    @1
    cc0
    @50
    @1
    @1
    cN
    elfznn
    #
    nnne0d
    #
    neneqd
    adantl
    iffalsed
    oveq2d
    sumeq2dv
    @46
    @47
    @0
    @12
    vk
    c1
    cc0
    cuz
    cfv
    #
    wcel
    @47
    @0
    wss
    @46
    1eluzge0
    c1
    cc0
    cN
    fzss1
    mp1i
    @51
    @2
    @11
    @46
    @27
    @28
    @26
    @50
    wph
    @27
    @23
    dvply1.a
    adantr
    #
    @50
    @1
    @52
    nnnn0d
    #
    @30
    syl2an
    #
    @51
    @11
    @10
    cc
    @51
    @7
    cc0
    @10
    @51
    @1
    cc0
    @50
    @1
    cc0
    wne
    @46
    @53
    adantl
    neneqd
    iffalsed
    @51
    @1
    @9
    @51
    @1
    @50
    @28
    @46
    @56
    adantl
    nn0cnd
    @51
    @3
    @8
    wph
    @23
    @50
    simplr
    @50
    @38
    @46
    @50
    @37
    @38
    @52
    @40
    syl
    adantl
    expcld
    mulcld
    #
    eqeltrd
    mulcld
    @46
    @1
    @0
    @47
    cdif
    wcel
    #
    wa
    #
    @12
    @2
    cc0
    cmul
    co
    #
    cc0
    @60
    @11
    cc0
    @2
    cmul
    @60
    @7
    cc0
    @10
    @60
    @1
    cc0
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    wcel
    #
    wn
    #
    @7
    @64
    wo
    #
    @7
    @59
    @65
    @46
    @59
    @50
    @64
    @1
    @0
    @47
    eldifn
    @63
    @47
    @1
    @62
    c1
    cN
    cfz
    0p1e1
    oveq1i
    eleq2i
    sylnibr
    adantl
    @60
    @22
    @66
    @59
    @22
    @46
    @1
    @0
    @47
    eldifi
    #
    adantl
    @60
    cN
    @54
    wcel
    #
    @22
    @66
    wb
    wph
    @68
    @23
    @59
    wph
    cN
    cn0
    @54
    dvply1.n
    nn0uz
    syl6eleq
    ad2antrr
    @1
    cc0
    cN
    elfzp12
    syl
    mpbid
    @64
    @7
    orel2
    sylc
    iftrued
    oveq2d
    @59
    @46
    @22
    @61
    cc0
    wceq
    @67
    @46
    @22
    wa
    @2
    @46
    @27
    @28
    @26
    @22
    @55
    @29
    @30
    syl2an
    mul01d
    sylan2
    eqtrd
    @46
    cc0
    cN
    fzfid
    fsumss
    @46
    c1
    c1
    cmin
    co
    #
    @41
    cfz
    co
    #
    vj
    cv
    #
    c1
    caddc
    co
    #
    cA
    cfv
    #
    @72
    @3
    @72
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    vj
    csu
    #
    @42
    @1
    c1
    caddc
    co
    #
    @79
    cA
    cfv
    #
    cmul
    co
    #
    @4
    cmul
    co
    #
    vk
    csu
    #
    @49
    @45
    @46
    @42
    @77
    vj
    csu
    @42
    @72
    @73
    cmul
    co
    #
    @3
    @71
    cexp
    co
    #
    cmul
    co
    #
    vj
    csu
    @78
    @83
    @46
    @42
    @77
    @86
    vj
    @46
    @71
    @42
    wcel
    #
    wa
    #
    @77
    @73
    @72
    @85
    cmul
    co
    #
    cmul
    co
    @73
    @72
    cmul
    co
    #
    @85
    cmul
    co
    @86
    @88
    @76
    @89
    @73
    cmul
    @88
    @75
    @85
    @72
    cmul
    @88
    @74
    @71
    @3
    cexp
    @88
    @71
    cc
    wcel
    c1
    cc
    wcel
    @74
    @71
    wceq
    @88
    @71
    @87
    @71
    cn0
    wcel
    #
    @46
    @71
    @41
    elfznn0
    #
    adantl
    #
    nn0cnd
    ax-1cn
    @71
    c1
    pncan
    sylancl
    oveq2d
    oveq2d
    oveq2d
    @88
    @73
    @72
    @85
    @88
    cn0
    cc
    @72
    cA
    wph
    @27
    @23
    @87
    dvply1.a
    ad2antrr
    @87
    @72
    cn0
    wcel
    #
    @46
    @87
    @91
    @94
    @92
    @71
    peano2nn0
    syl
    adantl
    #
    ffvelrnd
    #
    @88
    @72
    @95
    nn0cnd
    #
    @88
    @3
    @71
    wph
    @23
    @87
    simplr
    @93
    expcld
    mulassd
    @88
    @90
    @84
    @85
    cmul
    @88
    @73
    @72
    @96
    @97
    mulcomd
    oveq1d
    3eqtr2d
    sumeq2dv
    @70
    @42
    @77
    vj
    @69
    cc0
    @41
    cfz
    1m1e0
    oveq1i
    sumeq1i
    @42
    @82
    @86
    vk
    vj
    @1
    @71
    wceq
    #
    @81
    @84
    @4
    @85
    cmul
    @98
    @79
    @72
    @80
    @73
    cmul
    @1
    @71
    c1
    caddc
    oveq1
    #
    @98
    @79
    @72
    cA
    @99
    fveq2d
    oveq12d
    @1
    @71
    @3
    cexp
    oveq2
    oveq12d
    cbvsumv
    3eqtr4g
    @46
    @48
    @77
    vk
    vj
    c1
    c1
    cN
    @46
    1zzd
    #
    @100
    @46
    cN
    wph
    cN
    cn0
    wcel
    @23
    dvply1.n
    adantr
    nn0zd
    @51
    @2
    @10
    @57
    @58
    mulcld
    @1
    @72
    wceq
    #
    @2
    @73
    @10
    @76
    cmul
    @1
    @72
    cA
    fveq2
    @101
    @1
    @72
    @9
    @75
    cmul
    @101
    id
    @101
    @8
    @74
    @3
    cexp
    @1
    @72
    c1
    cmin
    oveq1
    oveq2d
    oveq12d
    oveq12d
    fsumshftm
    @46
    @42
    @44
    @82
    vk
    @46
    @1
    @42
    wcel
    #
    wa
    #
    @43
    @81
    @4
    cmul
    @103
    @28
    @81
    cvv
    wcel
    @43
    @81
    wceq
    @102
    @28
    @46
    @1
    @41
    elfznn0
    adantl
    @79
    @80
    cmul
    ovex
    vk
    cn0
    @81
    cvv
    cB
    dvply1.b
    fvmpt2
    sylancl
    oveq1d
    sumeq2dv
    3eqtr4d
    3eqtr3d
    mpteq2dva
    dvply1.g
    eqtr4d
    3eqtrd
end
