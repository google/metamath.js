include "caddc.mm"
include "cc0.mm"
include "cseq.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "cli.mm"
include "wbr.mm"
include "cmul.mm"
include "wceq.mm"
include "cc.mm"
include "wcel.mm"
include "addcld.mm"
include "efcvg.mm"
include "syl.mm"
include "cn0.mm"
include "cv.mm"
include "cexp.mm"
include "cfa.mm"
include "cdiv.mm"
include "csu.mm"
include "cabs.mm"
include "cmpt.mm"
include "eftval.mm"
include "adantl.mm"
include "wa.mm"
include "absexp.mm"
include "sylan.mm"
include "cn.mm"
include "faccl.mm"
include "nnre.mm"
include "nnnn0.mm"
include "nn0ge0d.mm"
include "absidd.mm"
include "oveq12d.mm"
include "expcl.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "absdivd.mm"
include "eqid.mm"
include "3eqtr4rd.mm"
include "eftcl.mm"
include "cfz.mm"
include "cmin.mm"
include "cbc.mm"
include "adantr.mm"
include "simpr.mm"
include "binom.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "fzfid.mm"
include "bccl2.mm"
include "ad2antrr.mm"
include "fznn0sub.mm"
include "expcld.mm"
include "elfznn0.mm"
include "mulcld.mm"
include "fsumdivc.mm"
include "divcld.mm"
include "eqeltrd.mm"
include "oveq2.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "fsumrev2.mm"
include "oveq2d.mm"
include "c1.mm"
include "nnmulcld.mm"
include "divrec2d.mm"
include "divmuldivd.mm"
include "bcval2.mm"
include "wne.mm"
include "divdiv32d.mm"
include "dividd.mm"
include "eqtrd.mm"
include "eqtr4d.mm"
include "nn0cn.mm"
include "ad2antlr.mm"
include "addid2d.mm"
include "nncand.mm"
include "div23d.mm"
include "sumeq2dv.mm"
include "cbvsumv.mm"
include "syl6eq.mm"
include "cdm.mm"
include "abscld.mm"
include "recnd.mm"
include "efcllem.mm"
include "mertens.mm"
include "efval.mm"
include "breqtrrd.mm"
include "climuni.mm"
include "syl2anc.mm"

theorem efaddlem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  assume efadd.1: |- F = ( n e. NN0 |-> ( ( A ^ n ) / ( ! ` n ) ) )
  assume efadd.2: |- G = ( n e. NN0 |-> ( ( B ^ n ) / ( ! ` n ) ) )
  assume efadd.3: |- H = ( n e. NN0 |-> ( ( ( A + B ) ^ n ) / ( ! ` n ) ) )
  assume efadd.4: |- ( ph -> A e. CC )
  assume efadd.5: |- ( ph -> B e. CC )

  disjoint A n
  disjoint B n
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint A j
  disjoint k m
  disjoint k n
  disjoint A k
  disjoint m n
  disjoint A m
  disjoint B j
  disjoint B k
  disjoint F j
  disjoint G j
  disjoint G k
  disjoint G m
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint H k
  assert |- ( ph -> ( exp ` ( A + B ) ) = ( ( exp ` A ) x. ( exp ` B ) ) )

  proof
    wph
    caddc
    cH
    cc0
    cseq
    #
    cA
    cB
    caddc
    co
    #
    ce
    cfv
    #
    cli
    wbr
    #
    @0
    cA
    ce
    cfv
    #
    cB
    ce
    cfv
    #
    cmul
    co
    #
    cli
    wbr
    @2
    @6
    wceq
    wph
    @1
    cc
    wcel
    @3
    wph
    cA
    cB
    efadd.4
    efadd.5
    addcld
    @1
    vn
    cH
    efadd.3
    efcvg
    syl
    wph
    @0
    cn0
    cA
    vj
    cv
    #
    cexp
    co
    #
    @7
    cfa
    cfv
    #
    cdiv
    co
    #
    vj
    csu
    #
    cn0
    cB
    vk
    cv
    #
    cexp
    co
    @12
    cfa
    cfv
    #
    cdiv
    co
    #
    vk
    csu
    #
    cmul
    co
    @6
    cli
    wph
    @10
    @14
    vj
    vk
    cF
    cG
    cH
    vn
    cn0
    cA
    cabs
    cfv
    #
    vn
    cv
    #
    cexp
    co
    @17
    cfa
    cfv
    cdiv
    co
    cmpt
    #
    @7
    cn0
    wcel
    #
    @7
    cF
    cfv
    @10
    wceq
    wph
    cA
    vn
    cF
    @7
    efadd.1
    eftval
    adantl
    wph
    @19
    wa
    #
    @8
    cabs
    cfv
    #
    @9
    cabs
    cfv
    #
    cdiv
    co
    @16
    @7
    cexp
    co
    #
    @9
    cdiv
    co
    #
    @10
    cabs
    cfv
    @7
    @18
    cfv
    #
    @20
    @21
    @23
    @22
    @9
    cdiv
    wph
    cA
    cc
    wcel
    #
    @19
    @21
    @23
    wceq
    efadd.4
    cA
    @7
    absexp
    sylan
    @20
    @9
    cn
    wcel
    #
    @22
    @9
    wceq
    @19
    @27
    wph
    @7
    faccl
    #
    adantl
    #
    @27
    @9
    @9
    nnre
    @27
    @9
    @9
    nnnn0
    nn0ge0d
    absidd
    syl
    oveq12d
    @20
    @8
    @9
    wph
    @26
    @19
    @8
    cc
    wcel
    efadd.4
    cA
    @7
    expcl
    sylan
    @20
    @9
    @29
    nncnd
    @20
    @9
    @29
    nnne0d
    absdivd
    @19
    @25
    @24
    wceq
    wph
    @16
    vn
    @18
    @7
    @18
    eqid
    #
    eftval
    adantl
    3eqtr4rd
    wph
    @26
    @19
    @10
    cc
    wcel
    efadd.4
    cA
    @7
    eftcl
    sylan
    @12
    cn0
    wcel
    #
    @12
    cG
    cfv
    @14
    wceq
    wph
    cB
    vn
    cG
    @12
    efadd.2
    eftval
    adantl
    wph
    cB
    cc
    wcel
    #
    @31
    @14
    cc
    wcel
    efadd.5
    cB
    @12
    eftcl
    sylan
    wph
    @31
    wa
    #
    @12
    cH
    cfv
    #
    @1
    @12
    cexp
    co
    #
    @13
    cdiv
    co
    #
    cc0
    @12
    cfz
    co
    #
    @10
    @12
    @7
    cmin
    co
    #
    cG
    cfv
    #
    cmul
    co
    #
    vj
    csu
    #
    @31
    @34
    @36
    wceq
    wph
    @1
    vn
    cH
    @12
    efadd.3
    eftval
    adantl
    @33
    @36
    @37
    @12
    @7
    cbc
    co
    #
    cA
    @38
    cexp
    co
    #
    cB
    @7
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
    @13
    cdiv
    co
    #
    @41
    @33
    @35
    @47
    @13
    cdiv
    @33
    @26
    @32
    @31
    @35
    @47
    wceq
    wph
    @26
    @31
    efadd.4
    adantr
    wph
    @32
    @31
    efadd.5
    adantr
    wph
    @31
    simpr
    cA
    cB
    vj
    @12
    binom
    syl3anc
    oveq1d
    @33
    @48
    @37
    @46
    @13
    cdiv
    co
    #
    vj
    csu
    #
    @41
    @33
    @37
    @46
    @13
    vj
    @33
    cc0
    @12
    fzfid
    @33
    @13
    @31
    @13
    cn
    wcel
    wph
    @12
    faccl
    adantl
    #
    nncnd
    #
    @33
    @7
    @37
    wcel
    #
    wa
    #
    @42
    @45
    @54
    @42
    @53
    @42
    cn
    wcel
    @33
    @7
    @12
    bccl2
    adantl
    nncnd
    #
    @54
    @43
    @44
    @54
    cA
    @38
    wph
    @26
    @31
    @53
    efadd.4
    ad2antrr
    #
    @53
    @38
    cn0
    wcel
    #
    @33
    @7
    cc0
    @12
    fznn0sub
    adantl
    #
    expcld
    #
    @54
    cB
    @7
    wph
    @32
    @31
    @53
    efadd.5
    ad2antrr
    #
    @53
    @19
    @33
    @7
    @12
    elfznn0
    adantl
    #
    expcld
    #
    mulcld
    #
    mulcld
    @33
    @13
    @51
    nnne0d
    #
    fsumdivc
    @33
    @41
    @37
    cA
    cc0
    @12
    caddc
    co
    #
    vm
    cv
    #
    cmin
    co
    #
    cexp
    co
    #
    @67
    cfa
    cfv
    #
    cdiv
    co
    #
    @12
    @67
    cmin
    co
    #
    cG
    cfv
    #
    cmul
    co
    #
    vm
    csu
    #
    @50
    @33
    @40
    @73
    vj
    vm
    cc0
    @12
    @54
    @10
    @39
    @54
    @8
    @9
    @54
    cA
    @7
    @56
    @61
    expcld
    @54
    @9
    @54
    @19
    @27
    @61
    @28
    syl
    #
    nncnd
    #
    @54
    @9
    @75
    nnne0d
    #
    divcld
    @54
    @39
    cB
    @38
    cexp
    co
    #
    @38
    cfa
    cfv
    #
    cdiv
    co
    #
    cc
    @54
    @57
    @39
    @80
    wceq
    @58
    cB
    vn
    cG
    @38
    efadd.2
    eftval
    syl
    @54
    @78
    @79
    @54
    cB
    @38
    @60
    @58
    expcld
    @54
    @79
    @54
    @57
    @79
    cn
    wcel
    @58
    @38
    faccl
    syl
    #
    nncnd
    #
    @54
    @79
    @81
    nnne0d
    #
    divcld
    eqeltrd
    mulcld
    @7
    @67
    wceq
    #
    @10
    @70
    @39
    @72
    cmul
    @84
    @8
    @68
    @9
    @69
    cdiv
    @7
    @67
    cA
    cexp
    oveq2
    @7
    @67
    cfa
    fveq2
    oveq12d
    @84
    @38
    @71
    cG
    @7
    @67
    @12
    cmin
    oveq2
    fveq2d
    oveq12d
    fsumrev2
    @33
    @50
    @37
    cA
    @65
    @7
    cmin
    co
    #
    cexp
    co
    #
    @85
    cfa
    cfv
    #
    cdiv
    co
    #
    @12
    @85
    cmin
    co
    #
    cG
    cfv
    #
    cmul
    co
    #
    vj
    csu
    @74
    @33
    @37
    @49
    @91
    vj
    @54
    @43
    @79
    cdiv
    co
    #
    @7
    cG
    cfv
    #
    cmul
    co
    #
    @42
    @13
    cdiv
    co
    #
    @45
    cmul
    co
    #
    @91
    @49
    @54
    @94
    @92
    @44
    @9
    cdiv
    co
    #
    cmul
    co
    #
    @96
    @54
    @93
    @97
    @92
    cmul
    @54
    @19
    @93
    @97
    wceq
    @61
    cB
    vn
    cG
    @7
    efadd.2
    eftval
    syl
    oveq2d
    @54
    @45
    @79
    @9
    cmul
    co
    #
    cdiv
    co
    c1
    @99
    cdiv
    co
    #
    @45
    cmul
    co
    @98
    @96
    @54
    @45
    @99
    @63
    @54
    @99
    @54
    @79
    @9
    @81
    @75
    nnmulcld
    #
    nncnd
    #
    @54
    @99
    @101
    nnne0d
    #
    divrec2d
    @54
    @43
    @79
    @44
    @9
    @59
    @82
    @62
    @76
    @83
    @77
    divmuldivd
    @54
    @95
    @100
    @45
    cmul
    @54
    @95
    @13
    @99
    cdiv
    co
    #
    @13
    cdiv
    co
    #
    @100
    @54
    @42
    @104
    @13
    cdiv
    @53
    @42
    @104
    wceq
    @33
    @7
    @12
    bcval2
    adantl
    oveq1d
    @54
    @105
    @13
    @13
    cdiv
    co
    #
    @99
    cdiv
    co
    @100
    @54
    @13
    @99
    @13
    @33
    @13
    cc
    wcel
    @53
    @52
    adantr
    #
    @102
    @107
    @103
    @33
    @13
    cc0
    wne
    @53
    @64
    adantr
    #
    divdiv32d
    @54
    @106
    c1
    @99
    cdiv
    @54
    @13
    @107
    @108
    dividd
    oveq1d
    eqtrd
    eqtrd
    oveq1d
    3eqtr4rd
    eqtr4d
    @54
    @88
    @92
    @90
    @93
    cmul
    @54
    @86
    @43
    @87
    @79
    cdiv
    @54
    @85
    @38
    cA
    cexp
    @54
    @65
    @12
    @7
    cmin
    @54
    @12
    @31
    @12
    cc
    wcel
    wph
    @53
    @12
    nn0cn
    ad2antlr
    #
    addid2d
    oveq1d
    #
    oveq2d
    @54
    @85
    @38
    cfa
    @110
    fveq2d
    oveq12d
    @54
    @89
    @7
    cG
    @54
    @89
    @12
    @38
    cmin
    co
    @7
    @54
    @85
    @38
    @12
    cmin
    @110
    oveq2d
    @54
    @12
    @7
    @109
    @54
    @19
    @7
    cc
    wcel
    @61
    @7
    nn0cn
    syl
    nncand
    eqtrd
    fveq2d
    oveq12d
    @54
    @42
    @45
    @13
    @55
    @63
    @107
    @108
    div23d
    3eqtr4rd
    sumeq2dv
    @37
    @91
    @73
    vj
    vm
    @7
    @66
    wceq
    #
    @88
    @70
    @90
    @72
    cmul
    @111
    @86
    @68
    @87
    @69
    cdiv
    @111
    @85
    @67
    cA
    cexp
    @7
    @66
    @65
    cmin
    oveq2
    #
    oveq2d
    @111
    @85
    @67
    cfa
    @112
    fveq2d
    oveq12d
    @111
    @89
    @71
    cG
    @111
    @85
    @67
    @12
    cmin
    @112
    oveq2d
    fveq2d
    oveq12d
    cbvsumv
    syl6eq
    eqtr4d
    eqtr4d
    eqtrd
    eqtrd
    wph
    @16
    cc
    wcel
    caddc
    @18
    cc0
    cseq
    cli
    cdm
    #
    wcel
    wph
    @16
    wph
    cA
    efadd.4
    abscld
    recnd
    @16
    vn
    @18
    @30
    efcllem
    syl
    wph
    @32
    caddc
    cG
    cc0
    cseq
    @113
    wcel
    efadd.5
    cB
    vn
    cG
    efadd.2
    efcllem
    syl
    mertens
    wph
    @4
    @11
    @5
    @15
    cmul
    wph
    @26
    @4
    @11
    wceq
    efadd.4
    cA
    vj
    efval
    syl
    wph
    @32
    @5
    @15
    wceq
    efadd.5
    cB
    vk
    efval
    syl
    oveq12d
    breqtrrd
    @2
    @6
    @0
    climuni
    syl2anc
end
