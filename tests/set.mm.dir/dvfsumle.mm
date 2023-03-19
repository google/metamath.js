include "cfzo.mm"
include "co.mm"
include "csu.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "csb.mm"
include "cmin.mm"
include "cle.mm"
include "cfn.mm"
include "wcel.mm"
include "fzofi.mm"
include "a1i.mm"
include "wa.mm"
include "cr.mm"
include "cfz.mm"
include "wral.mm"
include "cicc.mm"
include "cz.mm"
include "cin.mm"
include "wceq.mm"
include "cuz.mm"
include "cfv.mm"
include "eluzel2.mm"
include "syl.mm"
include "eluzelz.mm"
include "fzval2.mm"
include "syl2anc.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "sselda.mm"
include "cmpt.mm"
include "wf.mm"
include "ccncf.mm"
include "cncff.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "weq.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc.mm"
include "mpan9.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "fzofzp1.mm"
include "csbeq1.mm"
include "rspccva.mm"
include "syl2an.mm"
include "elfzofz.mm"
include "resubcld.mm"
include "cmul.mm"
include "cc.mm"
include "elfzoelz.mm"
include "adantl.mm"
include "zred.mm"
include "recnd.mm"
include "ax-1cn.mm"
include "pncan2.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "peano2re.mm"
include "subdid.mm"
include "mulid1d.mm"
include "3eqtr3d.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "mulcn.mm"
include "wss.mm"
include "wbr.mm"
include "adantr.mm"
include "elfzole1.mm"
include "elfzle2.mm"
include "iccss.mm"
include "syl22anc.mm"
include "iccssre.mm"
include "sstrd.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "cncfmptc.mm"
include "syl3anc.mm"
include "cncfmptid.mm"
include "remulcl.mm"
include "cncfmpt2ss.mm"
include "cioo.mm"
include "cdv.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "cxr.mm"
include "rexrd.mm"
include "iooss1.mm"
include "iooss2.mm"
include "ioossicc.mm"
include "syl5ss.mm"
include "1cnd.mm"
include "crn.mm"
include "ctg.mm"
include "dvmptid.mm"
include "ioossre.mm"
include "tgioo2.mm"
include "iooretop.mm"
include "dvmptres.mm"
include "dvmptcmul.mm"
include "mpteq2dv.mm"
include "eqtrd.mm"
include "nfcv.mm"
include "cbvmpt.mm"
include "cres.mm"
include "resmptd.mm"
include "rescncf.mm"
include "sylc.mm"
include "eqeltrrd.mm"
include "syl5eqelr.mm"
include "sseli.mm"
include "impcom.mm"
include "cdm.mm"
include "r19.21bi.mm"
include "adantlr.mm"
include "sylan2.mm"
include "fmptd.mm"
include "dvfre.mm"
include "dmeqd.mm"
include "dmmptg.mm"
include "feq12d.mm"
include "mpbid.mm"
include "oveq2i.mm"
include "3eqtr3g.mm"
include "anassrs.mm"
include "nfbr.mm"
include "breq2d.mm"
include "lep1d.mm"
include "lbicc2.mm"
include "ubicc2.mm"
include "oveq2.mm"
include "dvle.mm"
include "eqbrtrrd.mm"
include "fsumle.mm"
include "cvv.mm"
include "vex.mm"
include "eqeq2.mm"
include "biimpa.mm"
include "csbied.mm"
include "telfsumo2.mm"
include "breqtrd.mm"

theorem dvfsumle
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let vy: setvar y
  assume dvfsumle.m: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume dvfsumle.a: |- ( ph -> ( x e. ( M [,] N ) |-> A ) e. ( ( M [,] N ) -cn-> RR ) )
  assume dvfsumle.v: |- ( ( ph /\ x e. ( M (,) N ) ) -> B e. V )
  assume dvfsumle.b: |- ( ph -> ( RR _D ( x e. ( M (,) N ) |-> A ) ) = ( x e. ( M (,) N ) |-> B ) )
  assume dvfsumle.c: |- ( x = M -> A = C )
  assume dvfsumle.d: |- ( x = N -> A = D )
  assume dvfsumle.x: |- ( ( ph /\ k e. ( M ..^ N ) ) -> X e. RR )
  assume dvfsumle.l: |- ( ( ph /\ ( k e. ( M ..^ N ) /\ x e. ( k (,) ( k + 1 ) ) ) ) -> X <_ B )

  disjoint A k
  disjoint k x
  disjoint M k
  disjoint M x
  disjoint N k
  disjoint N x
  disjoint k ph
  disjoint ph x
  disjoint X x
  disjoint C x
  disjoint D x
  disjoint V x
  disjoint k y
  disjoint A y
  disjoint x y
  disjoint M y
  disjoint N y
  disjoint ph y
  disjoint X y
  disjoint B y
  disjoint C y
  disjoint D y
  assert |- ( ph -> sum_ k e. ( M ..^ N ) X <_ ( D - C ) )

  proof
    wph
    cM
    cN
    cfzo
    co
    #
    cX
    vk
    csu
    @0
    vx
    vk
    cv
    #
    c1
    caddc
    co
    #
    cA
    csb
    #
    vx
    @1
    cA
    csb
    #
    cmin
    co
    #
    vk
    csu
    cD
    cC
    cmin
    co
    cle
    wph
    @0
    cX
    @5
    vk
    @0
    cfn
    wcel
    wph
    cM
    cN
    fzofi
    a1i
    dvfsumle.x
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @3
    @4
    wph
    vx
    vy
    cv
    #
    cA
    csb
    #
    cr
    wcel
    #
    vy
    cM
    cN
    cfz
    co
    #
    wral
    #
    @2
    @11
    wcel
    #
    @3
    cr
    wcel
    #
    @6
    wph
    @10
    vy
    @11
    wph
    @8
    @11
    wcel
    #
    @8
    cM
    cN
    cicc
    co
    #
    wcel
    #
    @10
    wph
    @11
    @16
    @8
    wph
    @11
    @16
    cz
    cin
    #
    @16
    wph
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @11
    @18
    wceq
    wph
    cN
    cM
    cuz
    cfv
    wcel
    #
    @19
    dvfsumle.m
    cM
    cN
    eluzel2
    syl
    #
    wph
    @21
    @20
    dvfsumle.m
    cM
    cN
    eluzelz
    syl
    #
    cM
    cN
    fzval2
    syl2anc
    @16
    cz
    inss1
    syl6eqss
    sselda
    wph
    cA
    cr
    wcel
    #
    vx
    @16
    wral
    #
    @17
    @10
    wph
    @16
    cr
    vx
    @16
    cA
    cmpt
    #
    wf
    #
    @25
    wph
    @26
    @16
    cr
    ccncf
    co
    wcel
    #
    @27
    dvfsumle.a
    @16
    cr
    @26
    cncff
    syl
    #
    vx
    @16
    cr
    cA
    @26
    @26
    eqid
    fmpt
    #
    sylibr
    #
    @24
    @10
    vx
    @8
    @16
    vx
    @9
    cr
    vx
    @8
    cA
    nfcsb1v
    #
    nfel1
    vx
    vy
    weq
    #
    cA
    @9
    cr
    vx
    @8
    cA
    csbeq1a
    #
    eleq1d
    rspc
    #
    mpan9
    syldan
    #
    ralrimiva
    #
    cM
    cN
    @1
    fzofzp1
    #
    @10
    @14
    vy
    @2
    @11
    @8
    @2
    wceq
    @9
    @3
    cr
    vx
    @8
    @2
    cA
    csbeq1
    #
    eleq1d
    rspccva
    syl2an
    wph
    @12
    @1
    @11
    wcel
    @4
    cr
    wcel
    #
    @6
    @37
    @1
    cM
    cN
    elfzofz
    @10
    @40
    vy
    @1
    @11
    vy
    vk
    weq
    @9
    @4
    cr
    vx
    @8
    @1
    cA
    csbeq1
    #
    eleq1d
    rspccva
    syl2an
    resubcld
    @7
    cX
    @2
    cmul
    co
    #
    cX
    @1
    cmul
    co
    #
    cmin
    co
    #
    cX
    @5
    cle
    @7
    cX
    @2
    @1
    cmin
    co
    #
    cmul
    co
    cX
    c1
    cmul
    co
    #
    @44
    cX
    @7
    @45
    c1
    cX
    cmul
    @7
    @1
    cc
    wcel
    c1
    cc
    wcel
    @45
    c1
    wceq
    @7
    @1
    @7
    @1
    @6
    @1
    cz
    wcel
    wph
    @1
    cM
    cN
    elfzoelz
    adantl
    zred
    #
    recnd
    #
    ax-1cn
    @1
    c1
    pncan2
    sylancl
    oveq2d
    @7
    cX
    @2
    @1
    @7
    cX
    dvfsumle.x
    recnd
    #
    @7
    @2
    @7
    @1
    cr
    wcel
    @2
    cr
    wcel
    @47
    @1
    peano2re
    syl
    #
    recnd
    @48
    subdid
    @7
    cX
    @49
    mulid1d
    #
    3eqtr3d
    @7
    vy
    cX
    @8
    cmul
    co
    #
    cX
    @9
    vx
    @8
    cB
    csb
    #
    @43
    @4
    @42
    @3
    @1
    @2
    @1
    @2
    @47
    @50
    @7
    vy
    cX
    @8
    cr
    cmul
    ccnfld
    ctopn
    cfv
    #
    @1
    @2
    cicc
    co
    #
    @54
    eqid
    #
    @54
    @56
    mulcn
    @7
    cX
    cr
    wcel
    @55
    cc
    wss
    cr
    cc
    wss
    #
    vy
    @55
    cX
    cmpt
    @55
    cr
    ccncf
    co
    #
    wcel
    dvfsumle.x
    @7
    @55
    cr
    cc
    @7
    @55
    @16
    cr
    @7
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    cM
    @1
    cle
    wbr
    #
    @2
    cN
    cle
    wbr
    #
    @55
    @16
    wss
    #
    wph
    @59
    @6
    wph
    cM
    @22
    zred
    #
    adantr
    #
    wph
    @60
    @6
    wph
    cN
    @23
    zred
    #
    adantr
    #
    @6
    @61
    wph
    @1
    cM
    cN
    elfzole1
    adantl
    #
    @7
    @13
    @62
    @6
    @13
    wph
    @38
    adantl
    @2
    cM
    cN
    elfzle2
    syl
    #
    cM
    cN
    @1
    @2
    iccss
    syl22anc
    #
    wph
    @16
    cr
    wss
    #
    @6
    wph
    @59
    @60
    @71
    @64
    @66
    cM
    cN
    iccssre
    syl2anc
    adantr
    #
    sstrd
    #
    ax-resscn
    syl6ss
    @57
    @7
    ax-resscn
    a1i
    #
    vy
    cX
    @55
    cr
    cncfmptc
    syl3anc
    @7
    @55
    cr
    wss
    @57
    vy
    @55
    @8
    cmpt
    @58
    wcel
    @73
    ax-resscn
    vy
    @55
    cr
    cncfmptid
    sylancl
    ax-resscn
    cX
    @8
    remulcl
    cncfmpt2ss
    @7
    cr
    vy
    @1
    @2
    cioo
    co
    #
    @52
    cmpt
    cdv
    co
    vy
    @75
    @46
    cmpt
    vy
    @75
    cX
    cmpt
    @7
    vy
    @8
    c1
    cX
    cr
    cc
    @75
    cr
    cr
    cc
    cpr
    wcel
    @7
    reelprrecn
    a1i
    #
    @7
    @75
    cc
    @8
    @7
    @75
    cM
    cN
    cioo
    co
    #
    cc
    @7
    @75
    cM
    @2
    cioo
    co
    #
    @77
    @7
    cM
    cxr
    wcel
    @61
    @75
    @78
    wss
    @7
    cM
    @65
    rexrd
    @68
    cM
    @1
    @2
    iooss1
    syl2anc
    @7
    cN
    cxr
    wcel
    @62
    @78
    @77
    wss
    @7
    cN
    @67
    rexrd
    @69
    cM
    @2
    cN
    iooss2
    syl2anc
    sstrd
    #
    @7
    @77
    @16
    cc
    cM
    cN
    ioossicc
    #
    @7
    @16
    cr
    cc
    @72
    ax-resscn
    syl6ss
    syl5ss
    sstrd
    sselda
    @7
    @8
    @75
    wcel
    #
    wa
    1cnd
    @7
    vy
    @8
    c1
    cr
    cioo
    crn
    ctg
    cfv
    #
    @54
    cc
    cr
    @75
    @76
    @7
    cr
    cc
    @8
    @74
    sselda
    @7
    @8
    cr
    wcel
    wa
    1cnd
    @7
    vy
    cr
    @76
    dvmptid
    @75
    cr
    wss
    @7
    @1
    @2
    ioossre
    a1i
    @54
    @56
    tgioo2
    #
    @56
    @75
    @82
    wcel
    @7
    @1
    @2
    iooretop
    a1i
    #
    dvmptres
    @49
    dvmptcmul
    @7
    vy
    @75
    @46
    cX
    @51
    mpteq2dv
    eqtrd
    @7
    vy
    @55
    @9
    cmpt
    vx
    @55
    cA
    cmpt
    #
    @58
    vx
    vy
    @55
    cA
    @9
    vy
    cA
    nfcv
    #
    @32
    @34
    cbvmpt
    @7
    @26
    @55
    cres
    #
    @85
    @58
    @7
    vx
    @16
    @55
    cA
    @70
    resmptd
    @7
    @63
    @28
    @87
    @58
    wcel
    @70
    wph
    @28
    @6
    dvfsumle.a
    adantr
    @16
    cr
    @55
    @26
    rescncf
    sylc
    eqeltrrd
    syl5eqelr
    @7
    vy
    @9
    @53
    cr
    @82
    @54
    cr
    @77
    @75
    @76
    @7
    @8
    @77
    wcel
    #
    wa
    @9
    @7
    @25
    @17
    @10
    @88
    @7
    @27
    @25
    wph
    @27
    @6
    @29
    adantr
    @30
    sylibr
    @77
    @16
    @8
    @80
    sseli
    @17
    @25
    @10
    @35
    impcom
    syl2an
    recnd
    @7
    cB
    cr
    wcel
    #
    vx
    @77
    wral
    #
    @88
    @53
    cr
    wcel
    #
    @7
    @77
    cr
    vx
    @77
    cB
    cmpt
    #
    wf
    #
    @90
    @7
    cr
    vx
    @77
    cA
    cmpt
    #
    cdv
    co
    #
    cdm
    #
    cr
    @95
    wf
    #
    @93
    @7
    @77
    cr
    @94
    wf
    @77
    cr
    wss
    @97
    @7
    vx
    @77
    cA
    cr
    @94
    vx
    cv
    #
    @77
    wcel
    #
    @7
    @98
    @16
    wcel
    #
    @24
    @77
    @16
    @98
    @80
    sseli
    wph
    @100
    @24
    @6
    wph
    @24
    vx
    @16
    @31
    r19.21bi
    adantlr
    sylan2
    @94
    eqid
    fmptd
    cM
    cN
    ioossre
    @77
    @94
    dvfre
    sylancl
    @7
    @96
    @77
    cr
    @95
    @92
    wph
    @95
    @92
    wceq
    @6
    dvfsumle.b
    adantr
    #
    @7
    @96
    @92
    cdm
    #
    @77
    @7
    @95
    @92
    @101
    dmeqd
    @7
    cB
    cV
    wcel
    #
    vx
    @77
    wral
    @102
    @77
    wceq
    @7
    @103
    vx
    @77
    wph
    @99
    @103
    @6
    dvfsumle.v
    adantlr
    ralrimiva
    vx
    @77
    cB
    cV
    dmmptg
    syl
    eqtrd
    feq12d
    mpbid
    vx
    @77
    cr
    cB
    @92
    @92
    eqid
    fmpt
    sylibr
    @89
    @91
    vx
    @8
    @77
    vx
    @53
    cr
    vx
    @8
    cB
    nfcsb1v
    #
    nfel1
    @33
    cB
    @53
    cr
    vx
    @8
    cB
    csbeq1a
    #
    eleq1d
    rspc
    mpan9
    @7
    @95
    @92
    cr
    vy
    @77
    @9
    cmpt
    #
    cdv
    co
    vy
    @77
    @53
    cmpt
    @101
    @94
    @106
    cr
    cdv
    vx
    vy
    @77
    cA
    @9
    @86
    @32
    @34
    cbvmpt
    oveq2i
    vx
    vy
    @77
    cB
    @53
    vy
    cB
    nfcv
    @104
    @105
    cbvmpt
    3eqtr3g
    @79
    @83
    @56
    @84
    dvmptres
    @7
    cX
    cB
    cle
    wbr
    #
    vx
    @75
    wral
    @81
    cX
    @53
    cle
    wbr
    #
    @7
    @107
    vx
    @75
    wph
    @6
    @98
    @75
    wcel
    @107
    dvfsumle.l
    anassrs
    ralrimiva
    @107
    @108
    vx
    @8
    @75
    vx
    cX
    @53
    cle
    vx
    cX
    nfcv
    vx
    cle
    nfcv
    @104
    nfbr
    @33
    cB
    @53
    cX
    cle
    @105
    breq2d
    rspc
    mpan9
    @7
    @1
    cxr
    wcel
    #
    @2
    cxr
    wcel
    #
    @1
    @2
    cle
    wbr
    #
    @1
    @55
    wcel
    @7
    @1
    @47
    rexrd
    #
    @7
    @2
    @50
    rexrd
    #
    @7
    @1
    @47
    lep1d
    #
    @1
    @2
    lbicc2
    syl3anc
    @7
    @109
    @110
    @111
    @2
    @55
    wcel
    @112
    @113
    @114
    @1
    @2
    ubicc2
    syl3anc
    @114
    @8
    @1
    cX
    cmul
    oveq2
    @41
    @8
    @2
    cX
    cmul
    oveq2
    @39
    dvle
    eqbrtrrd
    fsumle
    wph
    @9
    @4
    @3
    cC
    vk
    vy
    cD
    cM
    cN
    @41
    @39
    @8
    cM
    wceq
    #
    vx
    @8
    cA
    cC
    cvv
    @8
    cvv
    wcel
    #
    @115
    vy
    vex
    #
    a1i
    @115
    @33
    wa
    @98
    cM
    wceq
    #
    cA
    cC
    wceq
    @115
    @33
    @118
    @8
    cM
    @98
    eqeq2
    biimpa
    dvfsumle.c
    syl
    csbied
    @8
    cN
    wceq
    #
    vx
    @8
    cA
    cD
    cvv
    @116
    @119
    @117
    a1i
    @119
    @33
    wa
    @98
    cN
    wceq
    #
    cA
    cD
    wceq
    @119
    @33
    @120
    @8
    cN
    @98
    eqeq2
    biimpa
    dvfsumle.d
    syl
    csbied
    dvfsumle.m
    wph
    @15
    wa
    @9
    @36
    recnd
    telfsumo2
    breqtrd
end
