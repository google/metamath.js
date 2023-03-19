include "cfz.mm"
include "co.mm"
include "cprod.mm"
include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "cmul.mm"
include "cseq.mm"
include "prodfc.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "ccom.mm"
include "fveq2.mm"
include "cn.mm"
include "cuz.mm"
include "wcel.mm"
include "cz.mm"
include "eluzelz.mm"
include "syl.mm"
include "zcnd.mm"
include "eluzel2.mm"
include "1cnd.mm"
include "subadd23d.mm"
include "eqcomd.mm"
include "cn0.mm"
include "uznn0sub.mm"
include "nn0p1nn.mm"
include "eqeltrd.mm"
include "wral.mm"
include "wceq.mm"
include "wreu.mm"
include "wf1o.mm"
include "wsbc.mm"
include "pncan3d.mm"
include "pnpncand.mm"
include "oveq12d.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "wa.mm"
include "cc.mm"
include "elfzelz.mm"
include "adantl.mm"
include "peano2zm.mm"
include "adantr.mm"
include "npcand.mm"
include "simpr.mm"
include "ovex.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "sbcie.mm"
include "sylibr.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "wb.mm"
include "1zzd.mm"
include "nnzd.mm"
include "fzshftral.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "wrex.mm"
include "weq.mm"
include "wi.mm"
include "fzsubel.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "nncand.mm"
include "subsub2d.mm"
include "eleqtrd.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "anim12i.mm"
include "eqtr2.mm"
include "simprl.mm"
include "simprr.mm"
include "addcan2d.mm"
include "syl5ib.mm"
include "sylan2.mm"
include "ralrimivva.mm"
include "reu4.mm"
include "sylanbrc.mm"
include "eqid.mm"
include "f1ompt.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "csb.mm"
include "fzaddel.mm"
include "nfcsb1v.mm"
include "nfeq2.mm"
include "csbeq1a.mm"
include "eqeq12d.mm"
include "rspc.mm"
include "mpan9.mm"
include "wf.mm"
include "f1of.mm"
include "fvco3.mm"
include "sylan.mm"
include "fvmpt.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "nfel1.mm"
include "fvmpts.mm"
include "3eqtr4d.mm"
include "fprod.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "seqshft2.mm"
include "seqeq1d.mm"
include "fveq12d.mm"
include "3eqtrd.mm"
include "syl5eqr.mm"

theorem fprodser
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  assume fprodser.1: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) = A )
  assume fprodser.2: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume fprodser.3: |- ( ( ph /\ k e. ( M ... N ) ) -> A e. CC )

  disjoint F k
  disjoint k ph
  disjoint M k
  disjoint N k
  disjoint A j
  disjoint A m
  disjoint F j
  disjoint F m
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j ph
  disjoint k m
  disjoint M j
  disjoint M m
  disjoint m n
  disjoint M n
  disjoint m p
  disjoint M p
  disjoint m ph
  disjoint N j
  disjoint N m
  disjoint N n
  disjoint n p
  disjoint N p
  disjoint n ph
  disjoint p ph
  assert |- ( ph -> prod_ k e. ( M ... N ) A = ( seq M ( x. , F ) ` N ) )

  proof
    wph
    cM
    cN
    cfz
    co
    #
    cA
    vk
    cprod
    @0
    vj
    cv
    #
    vk
    @0
    cA
    cmpt
    #
    cfv
    #
    vj
    cprod
    #
    cN
    cmul
    cF
    cM
    cseq
    #
    cfv
    #
    @0
    cA
    vj
    vk
    prodfc
    wph
    @4
    cN
    c1
    cM
    cmin
    co
    caddc
    co
    #
    cmul
    cF
    vn
    c1
    @7
    cfz
    co
    #
    vn
    cv
    #
    cM
    c1
    cmin
    co
    #
    caddc
    co
    #
    cmpt
    #
    ccom
    #
    c1
    cseq
    cfv
    @7
    @10
    caddc
    co
    #
    cmul
    cF
    c1
    @10
    caddc
    co
    #
    cseq
    #
    cfv
    @6
    wph
    @0
    @3
    vm
    cv
    #
    @12
    cfv
    #
    @2
    cfv
    #
    vj
    vm
    @12
    @13
    @7
    @1
    @18
    @2
    fveq2
    wph
    @7
    cN
    cM
    cmin
    co
    #
    c1
    caddc
    co
    #
    cn
    wph
    @21
    @7
    wph
    cN
    cM
    c1
    wph
    cN
    wph
    cN
    cM
    cuz
    cfv
    wcel
    #
    cN
    cz
    wcel
    #
    fprodser.2
    cM
    cN
    eluzelz
    syl
    #
    zcnd
    #
    wph
    cM
    wph
    @22
    cM
    cz
    wcel
    #
    fprodser.2
    cM
    cN
    eluzel2
    syl
    #
    zcnd
    #
    wph
    1cnd
    #
    subadd23d
    eqcomd
    wph
    @20
    cn0
    wcel
    #
    @21
    cn
    wcel
    wph
    @22
    @30
    fprodser.2
    cM
    cN
    uznn0sub
    syl
    @20
    nn0p1nn
    syl
    eqeltrd
    #
    wph
    @11
    @0
    wcel
    #
    vn
    @8
    wral
    #
    vp
    cv
    #
    @11
    wceq
    #
    vn
    @8
    wreu
    #
    vp
    @0
    wral
    @8
    @0
    @12
    wf1o
    #
    wph
    @33
    @32
    vn
    @34
    @10
    cmin
    co
    #
    wsbc
    #
    vp
    @15
    @14
    cfz
    co
    #
    wral
    #
    wph
    @39
    vp
    @40
    wph
    @34
    @40
    wcel
    #
    @34
    @0
    wcel
    #
    @39
    wph
    @42
    @43
    wph
    @40
    @0
    @34
    wph
    @15
    cM
    @14
    cN
    cfz
    wph
    c1
    cM
    @29
    @28
    pncan3d
    #
    wph
    cN
    c1
    cM
    @25
    @29
    @28
    pnpncand
    #
    oveq12d
    #
    eleq2d
    biimpa
    wph
    @43
    wa
    #
    @38
    @10
    caddc
    co
    #
    @0
    wcel
    #
    @39
    @47
    @48
    @34
    @0
    @47
    @34
    @10
    @43
    @34
    cc
    wcel
    wph
    @43
    @34
    @34
    cM
    cN
    elfzelz
    #
    zcnd
    adantl
    wph
    @10
    cc
    wcel
    #
    @43
    wph
    @10
    wph
    @26
    @10
    cz
    wcel
    #
    @27
    cM
    peano2zm
    syl
    #
    zcnd
    #
    adantr
    npcand
    #
    wph
    @43
    simpr
    #
    eqeltrd
    @32
    @49
    vn
    @38
    @34
    @10
    cmin
    ovex
    @9
    @38
    wceq
    #
    @11
    @48
    @0
    @9
    @38
    @10
    caddc
    oveq1
    #
    eleq1d
    sbcie
    sylibr
    syldan
    ralrimiva
    wph
    c1
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    @52
    @33
    @41
    wb
    wph
    1zzd
    wph
    @7
    @31
    nnzd
    #
    @53
    @32
    vn
    vp
    @10
    c1
    @7
    fzshftral
    syl3anc
    mpbird
    wph
    @36
    vp
    @0
    @47
    @35
    vn
    @8
    wrex
    #
    @35
    @34
    @17
    @10
    caddc
    co
    #
    wceq
    #
    wa
    #
    vn
    vm
    weq
    #
    wi
    #
    vm
    @8
    wral
    vn
    @8
    wral
    #
    @36
    @47
    @38
    @8
    wcel
    @34
    @48
    wceq
    #
    @62
    @47
    @38
    cM
    @10
    cmin
    co
    #
    cN
    @10
    cmin
    co
    #
    cfz
    co
    #
    @8
    @47
    @43
    @38
    @72
    wcel
    #
    @56
    @47
    @26
    @23
    @34
    cz
    wcel
    #
    @52
    @43
    @73
    wb
    wph
    @26
    @43
    @27
    adantr
    wph
    @23
    @43
    @24
    adantr
    @43
    @74
    wph
    @50
    adantl
    wph
    @52
    @43
    @53
    adantr
    @34
    @10
    cM
    cN
    fzsubel
    syl22anc
    mpbid
    wph
    @72
    @8
    wceq
    @43
    wph
    @70
    c1
    @71
    @7
    cfz
    wph
    cM
    c1
    @28
    @29
    nncand
    wph
    cN
    cM
    c1
    @25
    @28
    @29
    subsub2d
    oveq12d
    adantr
    eleqtrd
    @47
    @48
    @34
    @55
    eqcomd
    @35
    @69
    vn
    @38
    @8
    @57
    @11
    @48
    @34
    @58
    eqeq2d
    rspcev
    syl2anc
    wph
    @68
    @43
    wph
    @67
    vn
    vm
    @8
    @8
    @9
    @8
    wcel
    #
    @17
    @8
    wcel
    #
    wa
    wph
    @9
    cc
    wcel
    #
    @17
    cc
    wcel
    #
    wa
    #
    @67
    @75
    @77
    @76
    @78
    @75
    @9
    @9
    c1
    @7
    elfzelz
    zcnd
    @76
    @17
    @17
    c1
    @7
    elfzelz
    #
    zcnd
    anim12i
    @65
    @11
    @63
    wceq
    wph
    @79
    wa
    #
    @66
    @34
    @11
    @63
    eqtr2
    @81
    @9
    @17
    @10
    wph
    @77
    @78
    simprl
    wph
    @77
    @78
    simprr
    wph
    @51
    @79
    @54
    adantr
    addcan2d
    syl5ib
    sylan2
    ralrimivva
    adantr
    @35
    @64
    vn
    vm
    @8
    @66
    @11
    @63
    @34
    @9
    @17
    @10
    caddc
    oveq1
    #
    eqeq2d
    reu4
    sylanbrc
    ralrimiva
    vn
    vp
    @8
    @0
    @11
    @12
    @12
    eqid
    #
    f1ompt
    sylanbrc
    #
    wph
    @0
    cc
    @1
    @2
    wph
    vk
    @0
    cA
    cc
    @2
    fprodser.3
    @2
    eqid
    #
    fmptd
    ffvelrnda
    wph
    @76
    wa
    #
    @63
    cF
    cfv
    #
    vk
    @63
    cA
    csb
    #
    @17
    @13
    cfv
    #
    @19
    wph
    @76
    @63
    @0
    wcel
    #
    @87
    @88
    wceq
    #
    @86
    @63
    @40
    @0
    @86
    @76
    @63
    @40
    wcel
    #
    wph
    @76
    simpr
    @86
    @59
    @60
    @17
    cz
    wcel
    #
    @52
    @76
    @92
    wb
    @86
    1zzd
    wph
    @60
    @76
    @61
    adantr
    @76
    @93
    wph
    @80
    adantl
    wph
    @52
    @76
    @53
    adantr
    @17
    @10
    c1
    @7
    fzaddel
    syl22anc
    mpbid
    wph
    @40
    @0
    wceq
    @76
    @46
    adantr
    eleqtrd
    #
    wph
    vk
    cv
    #
    cF
    cfv
    #
    cA
    wceq
    #
    vk
    @0
    wral
    @90
    @91
    wph
    @97
    vk
    @0
    fprodser.1
    ralrimiva
    @97
    @91
    vk
    @63
    @0
    vk
    @87
    @88
    vk
    @63
    cA
    nfcsb1v
    #
    nfeq2
    @95
    @63
    wceq
    #
    @96
    @87
    cA
    @88
    @95
    @63
    cF
    fveq2
    vk
    @63
    cA
    csbeq1a
    #
    eqeq12d
    rspc
    mpan9
    syldan
    @86
    @89
    @18
    cF
    cfv
    #
    @87
    wph
    @8
    @0
    @12
    wf
    #
    @76
    @89
    @101
    wceq
    wph
    @37
    @102
    @84
    @8
    @0
    @12
    f1of
    syl
    @8
    @0
    @17
    cF
    @12
    fvco3
    sylan
    @86
    @18
    @63
    cF
    @76
    @18
    @63
    wceq
    wph
    vn
    @17
    @11
    @63
    @8
    @12
    @82
    @83
    @17
    @10
    caddc
    ovex
    fvmpt
    adantl
    #
    fveq2d
    eqtrd
    #
    @86
    @19
    @63
    @2
    cfv
    #
    @88
    @86
    @18
    @63
    @2
    @103
    fveq2d
    @86
    @90
    @88
    cc
    wcel
    #
    @105
    @88
    wceq
    @94
    wph
    @76
    @90
    @106
    @94
    wph
    cA
    cc
    wcel
    #
    vk
    @0
    wral
    @90
    @106
    wph
    @107
    vk
    @0
    fprodser.3
    ralrimiva
    @107
    @106
    vk
    @63
    @0
    vk
    @88
    cc
    @98
    nfel1
    @99
    cA
    @88
    cc
    @100
    eleq1d
    rspc
    mpan9
    syldan
    vk
    @63
    cA
    @0
    @2
    cc
    @85
    fvmpts
    syl2anc
    eqtrd
    3eqtr4d
    fprod
    wph
    cmul
    vm
    @13
    cF
    @10
    c1
    @7
    wph
    @7
    cn
    c1
    cuz
    cfv
    @31
    nnuz
    syl6eleq
    @53
    @104
    seqshft2
    wph
    @14
    cN
    @16
    @5
    wph
    @15
    cM
    cmul
    cF
    @44
    seqeq1d
    @45
    fveq12d
    3eqtrd
    syl5eqr
end
