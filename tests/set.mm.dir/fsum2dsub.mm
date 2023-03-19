include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cc0.mm"
include "csu.mm"
include "caddc.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cz.mm"
include "fzssz.mm"
include "simpr.mm"
include "sseldi.mm"
include "0zd.mm"
include "nn0zd.mm"
include "adantr.mm"
include "cneg.mm"
include "cuz.mm"
include "cfv.mm"
include "cc.mm"
include "simpll.mm"
include "wss.mm"
include "cn0.mm"
include "cn.mm"
include "fz1ssnn.mm"
include "nnssnn0.mm"
include "sstri.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "neg0.mm"
include "uzneg.mm"
include "syl5eqelr.mm"
include "fzss1.mm"
include "3syl.mm"
include "fzssuz.mm"
include "syl6ss.mm"
include "sselda.mm"
include "syl3anc.mm"
include "fsumshft.mm"
include "clt.mm"
include "wbr.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "nnnn0d.mm"
include "nn0addcld.mm"
include "nn0red.mm"
include "ltp1d.mm"
include "fzdisj.mm"
include "syl.mm"
include "cun.mm"
include "cle.mm"
include "zaddcld.mm"
include "cr.mm"
include "nnred.mm"
include "nn0addge2.mm"
include "syl2anc.mm"
include "elfzle2.mm"
include "adantl.mm"
include "leadd2dd.mm"
include "elfz4.mm"
include "syl32anc.mm"
include "fzsplit.mm"
include "fzfid.mm"
include "fz2ssnn0.mm"
include "sseldd.mm"
include "cmin.mm"
include "eleq1d.mm"
include "wral.mm"
include "simplr.mm"
include "an32s.mm"
include "ralrimiva.mm"
include "nnsscn.mm"
include "nn0cnd.mm"
include "negsubdi2d.mm"
include "eluzmn.mm"
include "eqeltrrd.mm"
include "rspcdva.mm"
include "syl21anc.mm"
include "fsumsplit.mm"
include "zcnd.mm"
include "addid2d.mm"
include "oveq1d.mm"
include "eqcomd.mm"
include "sumeq1d.mm"
include "sumeq2dv.mm"
include "cfn.mm"
include "fzfi.mm"
include "sumz.mm"
include "olcs.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "oveq12d.mm"
include "elfzuz3.mm"
include "eluzadd.mm"
include "zsscn.mm"
include "addcomd.mm"
include "fveq2d.mm"
include "3eltr3d.mm"
include "fzss2.mm"
include "eleqtrd.mm"
include "fsumcl.mm"
include "addid1d.mm"
include "3eqtrrd.mm"
include "cfzo.mm"
include "fzval3.mm"
include "ineq2d.mm"
include "fzodisj.mm"
include "peano2zd.mm"
include "nn0ge0d.mm"
include "zred.mm"
include "lep1d.mm"
include "letrd.mm"
include "fzosplit.mm"
include "uneq2d.mm"
include "3eqtr4d.mm"
include "simpl.mm"
include "adantrl.mm"
include "fz0ssnn0.mm"
include "simprl.mm"
include "anass1rs.mm"
include "fzofi.mm"
include "eqtrd.mm"
include "anasss.mm"
include "ancom2s.mm"
include "fsumcom.mm"

theorem fsum2dsub
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cN: class N
  assume fzsum2sub.m: |- ( ph -> M e. NN0 )
  assume fzsum2sub.n: |- ( ph -> N e. NN0 )
  assume fzsum2sub.1: |- ( i = ( k - j ) -> A = B )
  assume fzsum2sub.2: |- ( ( ph /\ i e. ( ZZ>= ` -u j ) /\ j e. ( 1 ... N ) ) -> A e. CC )
  assume fzsum2sub.3: |- ( ( ( ph /\ j e. ( 1 ... N ) ) /\ k e. ( ( ( M + j ) + 1 ) ... ( M + N ) ) ) -> B = 0 )
  assume fzsum2sub.4: |- ( ( ( ph /\ j e. ( 1 ... N ) ) /\ k e. ( 0 ..^ j ) ) -> B = 0 )

  disjoint A k
  disjoint B i
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint i ph
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> sum_ i e. ( 0 ... M ) sum_ j e. ( 1 ... N ) A = sum_ k e. ( 0 ... ( M + N ) ) sum_ j e. ( 1 ... N ) B )

  proof
    wph
    c1
    cN
    cfz
    co
    #
    cc0
    cM
    cfz
    co
    #
    cA
    vi
    csu
    #
    vj
    csu
    @0
    cc0
    cM
    cN
    caddc
    co
    #
    cfz
    co
    #
    cB
    vk
    csu
    #
    vj
    csu
    @1
    @0
    cA
    vj
    csu
    vi
    csu
    @4
    @0
    cB
    vj
    csu
    vk
    csu
    wph
    @0
    @2
    @5
    vj
    wph
    vj
    cv
    #
    @0
    wcel
    #
    wa
    #
    @2
    cc0
    @6
    caddc
    co
    #
    cM
    @6
    caddc
    co
    #
    cfz
    co
    #
    cB
    vk
    csu
    #
    @5
    @8
    cA
    cB
    vi
    vk
    @6
    cc0
    cM
    @8
    @0
    cz
    @6
    c1
    cN
    fzssz
    #
    wph
    @7
    simpr
    #
    sseldi
    #
    @8
    0zd
    #
    wph
    cM
    cz
    wcel
    #
    @7
    wph
    cM
    fzsum2sub.m
    nn0zd
    #
    adantr
    #
    @8
    vi
    cv
    #
    @1
    wcel
    #
    wa
    wph
    @20
    @6
    cneg
    #
    cuz
    cfv
    #
    wcel
    #
    @7
    cA
    cc
    wcel
    #
    wph
    @7
    @21
    simpll
    @8
    @1
    @23
    @20
    @8
    @1
    @22
    cM
    cfz
    co
    #
    @23
    @8
    @6
    cc0
    cuz
    cfv
    #
    wcel
    #
    cc0
    @23
    wcel
    @1
    @26
    wss
    @8
    @6
    cn0
    @27
    @8
    @0
    cn0
    @6
    @0
    cn
    cn0
    cN
    fz1ssnn
    #
    nnssnn0
    sstri
    #
    @14
    sseldi
    nn0uz
    syl6eleq
    @28
    cc0
    cc0
    cneg
    @23
    neg0
    cc0
    @6
    uzneg
    syl5eqelr
    cc0
    @22
    cM
    fzss1
    3syl
    @22
    cM
    fzssuz
    syl6ss
    sselda
    @8
    @7
    @21
    @14
    adantr
    fzsum2sub.2
    syl3anc
    #
    fzsum2sub.1
    fsumshft
    @8
    @12
    @6
    @3
    cfz
    co
    #
    cB
    vk
    csu
    #
    @5
    @8
    @33
    @6
    @10
    cfz
    co
    #
    cB
    vk
    csu
    #
    @10
    c1
    caddc
    co
    #
    @3
    cfz
    co
    #
    cB
    vk
    csu
    #
    caddc
    co
    @12
    cc0
    caddc
    co
    @12
    @8
    @34
    @37
    cB
    @32
    vk
    @8
    @10
    @36
    clt
    wbr
    @34
    @37
    cin
    c0
    wceq
    @8
    @10
    @8
    @10
    @8
    cM
    @6
    wph
    cM
    cn0
    wcel
    #
    @7
    fzsum2sub.m
    adantr
    #
    @8
    @6
    @8
    @0
    cn
    @6
    @29
    @14
    sseldi
    #
    nnnn0d
    #
    nn0addcld
    #
    nn0red
    ltp1d
    @6
    @10
    @36
    @3
    fzdisj
    syl
    @8
    @10
    @32
    wcel
    #
    @32
    @34
    @37
    cun
    wceq
    @8
    @6
    cz
    wcel
    #
    @3
    cz
    wcel
    #
    @10
    cz
    wcel
    @6
    @10
    cle
    wbr
    #
    @10
    @3
    cle
    wbr
    @44
    @15
    wph
    @46
    @7
    wph
    cM
    cN
    @18
    wph
    cN
    fzsum2sub.n
    nn0zd
    zaddcld
    adantr
    #
    @8
    @10
    @43
    nn0zd
    @8
    @6
    cr
    wcel
    @39
    @47
    @8
    @6
    @41
    nnred
    #
    @40
    @6
    cM
    nn0addge2
    syl2anc
    @8
    @6
    cN
    cM
    @49
    wph
    cN
    cr
    wcel
    #
    @7
    wph
    cN
    fzsum2sub.n
    nn0red
    #
    adantr
    #
    @8
    cM
    @40
    nn0red
    @7
    @6
    cN
    cle
    wbr
    wph
    @6
    c1
    cN
    elfzle2
    adantl
    #
    leadd2dd
    @10
    @6
    @3
    elfz4
    syl32anc
    @10
    @6
    @3
    fzsplit
    syl
    @8
    @6
    @3
    fzfid
    #
    @8
    vk
    cv
    #
    @32
    wcel
    #
    wa
    #
    wph
    @7
    @55
    cn0
    wcel
    #
    cB
    cc
    wcel
    #
    wph
    @7
    @56
    simpll
    @8
    @7
    @56
    @14
    adantr
    #
    @57
    @32
    cn0
    @55
    @57
    @6
    cn0
    wcel
    @32
    cn0
    wss
    @57
    @0
    cn0
    @6
    @30
    @60
    sseldi
    @6
    @3
    fz2ssnn0
    syl
    @8
    @56
    simpr
    sseldd
    #
    @8
    @58
    wa
    #
    @25
    @59
    vi
    @23
    @55
    @6
    cmin
    co
    #
    @20
    @63
    wceq
    cA
    cB
    cc
    fzsum2sub.1
    eleq1d
    @8
    @25
    vi
    @23
    wral
    @58
    @8
    @25
    vi
    @23
    wph
    @24
    @7
    @25
    wph
    @24
    wa
    #
    @7
    wa
    wph
    @24
    @7
    @25
    wph
    @24
    @7
    simpll
    wph
    @24
    @7
    simplr
    @64
    @7
    simpr
    fzsum2sub.2
    syl3anc
    an32s
    ralrimiva
    adantr
    @62
    @6
    @55
    cmin
    co
    #
    cneg
    #
    @63
    @23
    @62
    @6
    @55
    @62
    @0
    cc
    @6
    @0
    cn
    cc
    @29
    nnsscn
    sstri
    wph
    @7
    @58
    simplr
    #
    sseldi
    @62
    @55
    @8
    @58
    simpr
    #
    nn0cnd
    negsubdi2d
    @62
    @6
    @65
    cuz
    cfv
    wcel
    #
    @66
    @23
    wcel
    @62
    @45
    @58
    @69
    @62
    @0
    cz
    @6
    @13
    @67
    sseldi
    @68
    @6
    @55
    eluzmn
    syl2anc
    @65
    @6
    uzneg
    syl
    eqeltrrd
    rspcdva
    #
    syl21anc
    #
    fsumsplit
    @8
    @35
    @12
    @38
    cc0
    caddc
    @8
    @34
    @11
    cB
    vk
    @8
    @11
    @34
    @8
    @9
    @6
    @10
    cfz
    @8
    @6
    @8
    @6
    @15
    zcnd
    #
    addid2d
    oveq1d
    #
    eqcomd
    sumeq1d
    @8
    @38
    @37
    cc0
    vk
    csu
    #
    cc0
    @8
    @37
    cB
    cc0
    vk
    fzsum2sub.3
    sumeq2dv
    @37
    cfn
    wcel
    #
    @74
    cc0
    wceq
    #
    @36
    @3
    fzfi
    @37
    @27
    wss
    @75
    @76
    @37
    vk
    cc0
    sumz
    olcs
    ax-mp
    syl6eq
    oveq12d
    @8
    @12
    @8
    @11
    cB
    vk
    @8
    @9
    @10
    fzfid
    @8
    @55
    @11
    wcel
    #
    wa
    #
    wph
    @7
    @58
    @59
    wph
    @7
    @77
    simpll
    #
    @8
    @7
    @77
    @14
    adantr
    #
    @78
    wph
    @7
    @56
    @58
    @79
    @80
    @78
    @34
    @32
    @55
    @78
    @3
    @10
    cuz
    cfv
    #
    wcel
    #
    @34
    @32
    wss
    @8
    @82
    @77
    @8
    cN
    cM
    caddc
    co
    #
    @6
    cM
    caddc
    co
    #
    cuz
    cfv
    #
    @3
    @81
    @8
    cN
    @6
    cuz
    cfv
    wcel
    #
    @17
    @83
    @85
    wcel
    @7
    @86
    wph
    @6
    c1
    cN
    elfzuz3
    adantl
    @19
    cM
    @6
    cN
    eluzadd
    syl2anc
    @8
    cN
    cM
    wph
    cN
    cc
    wcel
    @7
    wph
    cN
    fzsum2sub.n
    nn0cnd
    adantr
    @8
    cz
    cc
    cM
    zsscn
    @19
    sseldi
    #
    addcomd
    @8
    @84
    @10
    cuz
    @8
    @6
    cM
    @72
    @87
    addcomd
    fveq2d
    3eltr3d
    adantr
    @10
    @6
    @3
    fzss2
    syl
    @78
    @55
    @11
    @34
    @8
    @77
    simpr
    @8
    @11
    @34
    wceq
    @77
    @73
    adantr
    eleqtrd
    sseldd
    @61
    syl21anc
    @70
    syl21anc
    fsumcl
    addid1d
    3eqtrrd
    @8
    @5
    cc0
    @6
    cfzo
    co
    #
    cB
    vk
    csu
    #
    @33
    caddc
    co
    cc0
    @33
    caddc
    co
    @33
    @8
    @88
    @32
    cB
    @4
    vk
    @8
    @88
    @32
    cin
    @88
    @6
    @3
    c1
    caddc
    co
    #
    cfzo
    co
    #
    cin
    c0
    @8
    @32
    @91
    @88
    @8
    @46
    @32
    @91
    wceq
    @48
    @6
    @3
    fzval3
    syl
    #
    ineq2d
    cc0
    @6
    @90
    fzodisj
    syl6eq
    @8
    cc0
    @90
    cfzo
    co
    #
    @88
    @91
    cun
    #
    @4
    @88
    @32
    cun
    @8
    @6
    cc0
    @90
    cfz
    co
    wcel
    #
    @93
    @94
    wceq
    @8
    cc0
    cz
    wcel
    @90
    cz
    wcel
    @45
    cc0
    @6
    cle
    wbr
    @6
    @90
    cle
    wbr
    @95
    @16
    @8
    @3
    @48
    peano2zd
    #
    @15
    @8
    @6
    @42
    nn0ge0d
    @8
    @6
    cN
    @90
    @49
    @52
    @8
    @90
    @96
    zred
    #
    @53
    @8
    cN
    @3
    @90
    @52
    @8
    @3
    @48
    zred
    #
    @97
    wph
    cN
    @3
    cle
    wbr
    #
    @7
    wph
    @50
    @39
    @99
    @51
    fzsum2sub.m
    cN
    cM
    nn0addge2
    syl2anc
    adantr
    @8
    @3
    @98
    lep1d
    letrd
    letrd
    @6
    cc0
    @90
    elfz4
    syl32anc
    cc0
    @90
    @6
    fzosplit
    syl
    @8
    @46
    @4
    @93
    wceq
    @48
    cc0
    @3
    fzval3
    syl
    @8
    @32
    @91
    @88
    @92
    uneq2d
    3eqtr4d
    wph
    @4
    cfn
    wcel
    @7
    wph
    cc0
    @3
    fzfid
    #
    adantr
    wph
    @55
    @4
    wcel
    #
    @7
    @59
    wph
    @101
    @7
    wa
    #
    wa
    #
    wph
    @7
    @58
    @59
    wph
    @102
    simpl
    wph
    @7
    @7
    @101
    @14
    adantrl
    @103
    @4
    cn0
    @55
    @3
    fz0ssnn0
    wph
    @101
    @7
    simprl
    sseldi
    @70
    syl21anc
    #
    anass1rs
    fsumsplit
    @8
    @89
    cc0
    @33
    caddc
    @8
    @89
    @88
    cc0
    vk
    csu
    #
    cc0
    @8
    @88
    cB
    cc0
    vk
    fzsum2sub.4
    sumeq2dv
    @88
    cfn
    wcel
    #
    @105
    cc0
    wceq
    #
    cc0
    @6
    fzofi
    @88
    @27
    wss
    @106
    @107
    @88
    vk
    cc0
    sumz
    olcs
    ax-mp
    syl6eq
    oveq1d
    @8
    @33
    @8
    @32
    cB
    vk
    @54
    @71
    fsumcl
    addid2d
    3eqtrrd
    eqtrd
    eqtrd
    sumeq2dv
    wph
    @1
    @0
    cA
    vi
    vj
    wph
    cc0
    cM
    fzfid
    wph
    c1
    cN
    fzfid
    #
    wph
    @7
    @21
    @25
    wph
    @7
    @21
    @25
    @31
    anasss
    ancom2s
    fsumcom
    wph
    @4
    @0
    cB
    vk
    vj
    @100
    @108
    @104
    fsumcom
    3eqtr4d
end
