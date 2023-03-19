include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cbcc.mm"
include "cmin.mm"
include "ccxp.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "caddc.mm"
include "cc.mm"
include "cbc.mm"
include "wceq.mm"
include "wi.mm"
include "rpcnd.mm"
include "recnd.mm"
include "binom.mm"
include "3expia.mm"
include "syl2anc.mm"
include "imp.mm"
include "adantr.mm"
include "addcld.mm"
include "simpr.mm"
include "cxpexp.mm"
include "elfznn0.mm"
include "simplr.mm"
include "bccbc.mm"
include "sylan2.mm"
include "ad2antrr.mm"
include "cle.mm"
include "wbr.mm"
include "elfzle2.mm"
include "adantl.mm"
include "wb.mm"
include "nn0sub.mm"
include "ancoms.mm"
include "adantll.mm"
include "mpbid.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "sumeq2dv.mm"
include "3eqtr4d.mm"
include "cxpcld.mm"
include "eqeltrrd.mm"
include "addid1d.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "cmpt.mm"
include "nn0uz.mm"
include "eqid.mm"
include "1nn0.mm"
include "a1i.mm"
include "nn0addcld.mm"
include "eqidd.mm"
include "oveq2d.mm"
include "bcccl.mm"
include "nn0cnd.mm"
include "subcld.mm"
include "expcld.mm"
include "mulcld.mm"
include "fvmptd.mm"
include "csn.mm"
include "cxp.mm"
include "peano2nn0.mm"
include "cr.mm"
include "wf.mm"
include "c0ex.mm"
include "fconst.mm"
include "0red.mm"
include "snssd.mm"
include "fssd.mm"
include "ffvelrnda.mm"
include "eqeltrd.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "wrel.mm"
include "climrel.mm"
include "xpeq1i.mm"
include "seqeq3.mm"
include "ax-mp.mm"
include "cz.mm"
include "0z.mm"
include "serclim0.mm"
include "eqbrtri.mm"
include "releldm.mm"
include "mp2an.mm"
include "cabs.mm"
include "eluznn0.mm"
include "sylan.mm"
include "syldan.mm"
include "0zd.mm"
include "nn0zd.mm"
include "1zzd.mm"
include "zsubcld.mm"
include "nn0ge0d.mm"
include "eluzle.mm"
include "zred.mm"
include "1red.mm"
include "nn0red.mm"
include "leaddsub.mm"
include "syl3anc.mm"
include "elfz4.mm"
include "syl32anc.mm"
include "bcc0.mm"
include "mpbird.mm"
include "eluzelcn.mm"
include "mul02d.mm"
include "eqtrd.mm"
include "abs00bd.mm"
include "0re.mm"
include "syl6eqel.mm"
include "eqle.mm"
include "breqtrrd.mm"
include "cvgcmpce.mm"
include "isumsplit.mm"
include "1cnd.mm"
include "pncand.mm"
include "sumeq1d.mm"
include "wss.mm"
include "cfn.mm"
include "wo.mm"
include "ssid.mm"
include "orci.mm"
include "sumz.mm"
include "syl6eq.mm"
include "3eqtrd.mm"
include "3eqtr4rd.mm"

theorem binomcxplemnn0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vj: setvar j
  assume binomcxp.a: |- ( ph -> A e. RR+ )
  assume binomcxp.b: |- ( ph -> B e. RR )
  assume binomcxp.lt: |- ( ph -> ( abs ` B ) < ( abs ` A ) )
  assume binomcxp.c: |- ( ph -> C e. CC )

  disjoint k ph
  disjoint A k
  disjoint B k
  disjoint C k
  disjoint j k
  disjoint j ph
  disjoint A j
  disjoint B j
  disjoint C j
  assert |- ( ( ph /\ C e. NN0 ) -> ( ( A + B ) ^c C ) = sum_ k e. NN0 ( ( C _Cc k ) x. ( ( A ^c ( C - k ) ) x. ( B ^ k ) ) ) )

  proof
    wph
    cC
    cn0
    wcel
    #
    wa
    #
    cc0
    cC
    cfz
    co
    #
    cC
    vk
    cv
    #
    cbcc
    co
    #
    cA
    cC
    @3
    cmin
    co
    #
    ccxp
    co
    #
    cB
    @3
    cexp
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cc0
    caddc
    co
    #
    @10
    cn0
    @9
    vk
    csu
    #
    cA
    cB
    caddc
    co
    #
    cC
    ccxp
    co
    #
    @1
    @10
    @1
    @14
    @10
    cc
    @1
    @13
    cC
    cexp
    co
    #
    @2
    cC
    @3
    cbc
    co
    #
    cA
    @5
    cexp
    co
    #
    @7
    cmul
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    @14
    @10
    wph
    @0
    @15
    @20
    wceq
    #
    wph
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @0
    @21
    wi
    wph
    cA
    binomcxp.a
    rpcnd
    #
    wph
    cB
    binomcxp.b
    recnd
    #
    @22
    @23
    @0
    @21
    cA
    cB
    vk
    cC
    binom
    3expia
    syl2anc
    imp
    @1
    @13
    cc
    wcel
    @0
    @14
    @15
    wceq
    @1
    cA
    cB
    wph
    @22
    @0
    @24
    adantr
    wph
    @23
    @0
    @25
    adantr
    addcld
    #
    wph
    @0
    simpr
    #
    @13
    cC
    cxpexp
    syl2anc
    @1
    @2
    @9
    @19
    vk
    @1
    @3
    @2
    wcel
    #
    wa
    #
    @4
    @16
    @8
    @18
    cmul
    @28
    @1
    @3
    cn0
    wcel
    #
    @4
    @16
    wceq
    @3
    cC
    elfznn0
    #
    @1
    @30
    wa
    #
    @3
    cC
    wph
    @0
    @30
    simplr
    @1
    @30
    simpr
    #
    bccbc
    sylan2
    @29
    @6
    @17
    @7
    cmul
    @29
    @22
    @5
    cn0
    wcel
    #
    @6
    @17
    wceq
    wph
    @22
    @0
    @28
    @24
    ad2antrr
    @29
    @3
    cC
    cle
    wbr
    #
    @34
    @28
    @35
    @1
    @3
    cc0
    cC
    elfzle2
    adantl
    @28
    @1
    @30
    @35
    @34
    wb
    #
    @31
    @0
    @30
    @36
    wph
    @30
    @0
    @36
    @3
    cC
    nn0sub
    ancoms
    adantll
    sylan2
    mpbid
    cA
    @5
    cxpexp
    syl2anc
    oveq1d
    oveq12d
    sumeq2dv
    3eqtr4d
    #
    @1
    @13
    cC
    @26
    wph
    cC
    cc
    wcel
    #
    @0
    binomcxp.c
    adantr
    #
    cxpcld
    eqeltrrd
    addid1d
    @1
    @12
    cc0
    cC
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    cfz
    co
    #
    @9
    vk
    csu
    #
    @40
    cuz
    cfv
    #
    @9
    vk
    csu
    #
    caddc
    co
    @10
    @45
    caddc
    co
    @11
    @1
    @9
    vk
    vj
    cn0
    cC
    vj
    cv
    #
    cbcc
    co
    #
    cA
    cC
    @46
    cmin
    co
    #
    ccxp
    co
    #
    cB
    @46
    cexp
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    cmpt
    #
    cc0
    @40
    @44
    cn0
    nn0uz
    @44
    eqid
    @1
    cC
    c1
    @27
    c1
    cn0
    wcel
    @1
    1nn0
    a1i
    nn0addcld
    @32
    vj
    @3
    @52
    @9
    cn0
    @53
    cc
    @32
    @53
    eqidd
    @32
    @46
    @3
    wceq
    #
    wa
    #
    @47
    @4
    @51
    @8
    cmul
    @55
    @46
    @3
    cC
    cbcc
    @32
    @54
    simpr
    #
    oveq2d
    @55
    @49
    @6
    @50
    @7
    cmul
    @55
    @48
    @5
    cA
    ccxp
    @55
    @46
    @3
    cC
    cmin
    @56
    oveq2d
    oveq2d
    @55
    @46
    @3
    cB
    cexp
    @56
    oveq2d
    oveq12d
    oveq12d
    @33
    @32
    @4
    @8
    @32
    cC
    @3
    wph
    @38
    @0
    @30
    binomcxp.c
    ad2antrr
    #
    @33
    bcccl
    @32
    @6
    @7
    @32
    cA
    @5
    wph
    @22
    @0
    @30
    @24
    ad2antrr
    @32
    cC
    @3
    @57
    @32
    @3
    @33
    nn0cnd
    subcld
    cxpcld
    @32
    cB
    @3
    wph
    @23
    @0
    @30
    @25
    ad2antrr
    @33
    expcld
    mulcld
    mulcld
    #
    fvmptd
    #
    @58
    @1
    cc0
    vk
    cn0
    cc0
    csn
    #
    cxp
    #
    @53
    cc0
    @40
    cn0
    nn0uz
    @0
    @40
    cn0
    wcel
    #
    wph
    cC
    peano2nn0
    adantl
    #
    @1
    cn0
    cr
    @3
    @61
    @1
    cn0
    @60
    cr
    @61
    cn0
    @60
    @61
    wf
    @1
    cn0
    cc0
    c0ex
    fconst
    a1i
    @1
    cc0
    cr
    @1
    0red
    #
    snssd
    fssd
    ffvelrnda
    #
    @32
    @3
    @53
    cfv
    #
    @9
    cc
    @59
    @58
    eqeltrd
    caddc
    @61
    cc0
    cseq
    #
    cli
    cdm
    wcel
    #
    @1
    cli
    wrel
    @67
    cc0
    cli
    wbr
    @68
    climrel
    @67
    caddc
    cc0
    cuz
    cfv
    #
    @60
    cxp
    #
    cc0
    cseq
    #
    cc0
    cli
    @61
    @70
    wceq
    @67
    @71
    wceq
    cn0
    @69
    @60
    nn0uz
    xpeq1i
    caddc
    @61
    @70
    cc0
    seqeq3
    ax-mp
    cc0
    cz
    wcel
    #
    @71
    cc0
    cli
    wbr
    0z
    cc0
    serclim0
    ax-mp
    eqbrtri
    @67
    cc0
    cli
    releldm
    mp2an
    a1i
    @64
    @1
    @3
    @44
    wcel
    #
    wa
    #
    @66
    cabs
    cfv
    #
    cc0
    cc0
    @3
    @61
    cfv
    #
    cmul
    co
    cle
    @74
    @75
    cr
    wcel
    @75
    cc0
    wceq
    @75
    cc0
    cle
    wbr
    @74
    @75
    cc0
    cr
    @74
    @66
    @74
    @66
    @9
    cc0
    @1
    @73
    @30
    @66
    @9
    wceq
    @1
    @62
    @73
    @30
    @63
    @3
    @40
    eluznn0
    sylan
    #
    @59
    syldan
    @74
    @9
    cc0
    @8
    cmul
    co
    cc0
    @74
    @4
    cc0
    @8
    cmul
    @74
    @4
    cc0
    wceq
    cC
    cc0
    @3
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    @74
    @72
    @78
    cz
    wcel
    cC
    cz
    wcel
    #
    cc0
    cC
    cle
    wbr
    #
    cC
    @78
    cle
    wbr
    #
    @79
    @74
    0zd
    @74
    @3
    c1
    @74
    @3
    @77
    nn0zd
    @74
    1zzd
    zsubcld
    @1
    @80
    @73
    @1
    cC
    @27
    nn0zd
    adantr
    #
    @1
    @81
    @73
    @1
    cC
    @27
    nn0ge0d
    adantr
    @74
    @40
    @3
    cle
    wbr
    #
    @82
    @73
    @84
    @1
    @40
    @3
    eluzle
    adantl
    @74
    cC
    cr
    wcel
    c1
    cr
    wcel
    @3
    cr
    wcel
    @84
    @82
    wb
    @74
    cC
    @83
    zred
    @74
    1red
    @74
    @3
    @77
    nn0red
    cC
    c1
    @3
    leaddsub
    syl3anc
    mpbid
    cC
    cc0
    @78
    elfz4
    syl32anc
    @74
    cC
    @3
    wph
    @38
    @0
    @73
    binomcxp.c
    ad2antrr
    #
    @77
    bcc0
    mpbird
    oveq1d
    @74
    @8
    @74
    @6
    @7
    @74
    cA
    @5
    wph
    @22
    @0
    @73
    @24
    ad2antrr
    @74
    cC
    @3
    @85
    @73
    @3
    cc
    wcel
    @1
    @40
    @3
    eluzelcn
    adantl
    subcld
    cxpcld
    @74
    cB
    @3
    wph
    @23
    @0
    @73
    @25
    ad2antrr
    @77
    expcld
    mulcld
    mul02d
    eqtrd
    #
    eqtrd
    abs00bd
    #
    0re
    syl6eqel
    @87
    @75
    cc0
    eqle
    syl2anc
    @74
    @76
    @1
    @73
    @30
    @76
    cc
    wcel
    @77
    @32
    @76
    @65
    recnd
    syldan
    mul02d
    breqtrrd
    cvgcmpce
    isumsplit
    @1
    @43
    @10
    @45
    caddc
    @1
    @42
    @2
    @9
    vk
    @1
    @41
    cC
    cc0
    cfz
    @1
    cC
    c1
    @39
    @1
    1cnd
    pncand
    oveq2d
    sumeq1d
    oveq1d
    @1
    @45
    cc0
    @10
    caddc
    @1
    @45
    @44
    cc0
    vk
    csu
    #
    cc0
    @1
    @44
    @9
    cc0
    vk
    @86
    sumeq2dv
    @44
    @44
    wss
    #
    @44
    cfn
    wcel
    #
    wo
    @88
    cc0
    wceq
    @89
    @90
    @44
    ssid
    orci
    @44
    vk
    @40
    sumz
    ax-mp
    syl6eq
    oveq2d
    3eqtrd
    @37
    3eqtr4rd
end
