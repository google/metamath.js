include "cem.mm"
include "c1.mm"
include "c2.mm"
include "clog.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cicc.mm"
include "wcel.mm"
include "cn.mm"
include "wf.mm"
include "w3a.mm"
include "wtru.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cli.mm"
include "emcllem6.mm"
include "simpri.mm"
include "a1i.mm"
include "cv.mm"
include "emcllem1.mm"
include "ffvelrni.mm"
include "adantl.mm"
include "climrecl.mm"
include "wral.mm"
include "1nn.mm"
include "wa.mm"
include "simpr.mm"
include "caddc.mm"
include "emcllem2.mm"
include "simprd.mm"
include "climub.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "fveq2.mm"
include "cfz.mm"
include "cdiv.mm"
include "csu.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "cz.mm"
include "cc.mm"
include "1z.mm"
include "ax-1cn.mm"
include "1div1e1.mm"
include "syl6eq.mm"
include "fsum1.mm"
include "mp2an.mm"
include "oveq1.mm"
include "df-2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "1re.mm"
include "crp.mm"
include "2rp.mm"
include "relogcl.mm"
include "ax-mp.mm"
include "resubcli.mm"
include "elexi.mm"
include "fvmpt.mm"
include "breq1d.mm"
include "rspcva.mm"
include "sylancr.mm"
include "cneg.mm"
include "cc0.mm"
include "cmpt.mm"
include "negeqd.mm"
include "eqid.mm"
include "negex.mm"
include "cvv.mm"
include "simpli.mm"
include "0cnd.mm"
include "nnex.mm"
include "mptex.mm"
include "recnd.mm"
include "df-neg.mm"
include "climsubc2.mm"
include "adantr.mm"
include "renegcld.mm"
include "eqeltrd.mm"
include "adantlr.mm"
include "simpld.mm"
include "peano2nn.mm"
include "syl.mm"
include "lenegd.mm"
include "mpbid.mm"
include "3brtr4d.mm"
include "eqbrtrrd.mm"
include "syl6breqr.mm"
include "wb.mm"
include "trud.mm"
include "leneg.mm"
include "mpbird.mm"
include "log1.mm"
include "1m0e1.mm"
include "breq2d.mm"
include "elicc2i.mm"
include "syl3anbrc.mm"
include "wfn.mm"
include "ffn.mm"
include "mp1i.mm"
include "cuz.mm"
include "syl6eleq.mm"
include "elfznn.mm"
include "monoord2.mm"
include "syl6breq.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "monoord.mm"
include "syl5eqbrr.mm"
include "3jca.mm"

theorem emcllem7
  let cT: class T
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x
  let cN: class N
  assume emcl.1: |- F = ( n e. NN |-> ( sum_ m e. ( 1 ... n ) ( 1 / m ) - ( log ` n ) ) )
  assume emcl.2: |- G = ( n e. NN |-> ( sum_ m e. ( 1 ... n ) ( 1 / m ) - ( log ` ( n + 1 ) ) ) )
  assume emcl.3: |- H = ( n e. NN |-> ( log ` ( 1 + ( 1 / n ) ) ) )
  assume emcl.4: |- T = ( n e. NN |-> ( ( 1 / n ) - ( log ` ( 1 + ( 1 / n ) ) ) ) )

  disjoint H m
  disjoint m n
  disjoint T m
  disjoint T n
  disjoint i k
  disjoint i x
  disjoint F i
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint G i
  disjoint G k
  disjoint G x
  disjoint k m
  disjoint H k
  disjoint N m
  disjoint N n
  disjoint k n
  disjoint T k
  disjoint m x
  disjoint n x
  disjoint T x
  assert |- ( gamma e. ( ( 1 - ( log ` 2 ) ) [,] 1 ) /\ F : NN --> ( gamma [,] 1 ) /\ G : NN --> ( ( 1 - ( log ` 2 ) ) [,] gamma ) )

  proof
    cem
    c1
    c2
    clog
    cfv
    #
    cmin
    co
    #
    c1
    cicc
    co
    wcel
    #
    cn
    cem
    c1
    cicc
    co
    #
    cF
    wf
    #
    cn
    @1
    cem
    cicc
    co
    #
    cG
    wf
    #
    w3a
    wtru
    @2
    @4
    @6
    wtru
    cem
    cr
    wcel
    #
    @1
    cem
    cle
    wbr
    #
    cem
    c1
    cle
    wbr
    #
    @2
    wtru
    cem
    vk
    cG
    c1
    cn
    nnuz
    wtru
    1zzd
    #
    cG
    cem
    cli
    wbr
    #
    wtru
    cF
    cem
    cli
    wbr
    #
    @11
    cT
    vm
    vn
    cF
    cG
    cH
    emcl.1
    emcl.2
    emcl.3
    emcl.4
    emcllem6
    #
    simpri
    #
    a1i
    vk
    cv
    #
    cn
    wcel
    #
    @15
    cG
    cfv
    #
    cr
    wcel
    #
    wtru
    cn
    cr
    @15
    cG
    cn
    cr
    cF
    wf
    #
    cn
    cr
    cG
    wf
    #
    vm
    vn
    cF
    cG
    emcl.1
    emcl.2
    emcllem1
    #
    simpri
    #
    ffvelrni
    #
    adantl
    climrecl
    #
    wtru
    c1
    cn
    wcel
    #
    vi
    cv
    #
    cG
    cfv
    #
    cem
    cle
    wbr
    #
    vi
    cn
    wral
    @8
    1nn
    wtru
    @28
    vi
    cn
    wtru
    @26
    cn
    wcel
    #
    wa
    #
    cem
    vk
    cG
    c1
    @26
    cn
    nnuz
    wtru
    @29
    simpr
    #
    @11
    @30
    @14
    a1i
    @16
    @18
    @30
    @23
    adantl
    @16
    @17
    @15
    c1
    caddc
    co
    #
    cG
    cfv
    cle
    wbr
    #
    @30
    @16
    @32
    cF
    cfv
    #
    @15
    cF
    cfv
    #
    cle
    wbr
    #
    @33
    vm
    vn
    cF
    cG
    @15
    emcl.1
    emcl.2
    emcllem2
    #
    simprd
    #
    adantl
    climub
    #
    ralrimiva
    @28
    @8
    vi
    c1
    cn
    @26
    c1
    wceq
    #
    @27
    @1
    cem
    cle
    @40
    @27
    c1
    cG
    cfv
    #
    @1
    @26
    c1
    cG
    fveq2
    @25
    @41
    @1
    wceq
    1nn
    vn
    c1
    c1
    vn
    cv
    #
    cfz
    co
    #
    c1
    vm
    cv
    #
    cdiv
    co
    #
    vm
    csu
    #
    @42
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    @1
    cn
    cG
    @42
    c1
    wceq
    #
    @46
    c1
    @48
    @0
    cmin
    @49
    @46
    c1
    c1
    cfz
    co
    #
    @45
    vm
    csu
    #
    c1
    @49
    @43
    @50
    @45
    vm
    @42
    c1
    c1
    cfz
    oveq2
    sumeq1d
    c1
    cz
    wcel
    c1
    cc
    wcel
    @51
    c1
    wceq
    1z
    ax-1cn
    @45
    c1
    vm
    c1
    @44
    c1
    wceq
    @45
    c1
    c1
    cdiv
    co
    c1
    @44
    c1
    c1
    cdiv
    oveq2
    1div1e1
    syl6eq
    fsum1
    mp2an
    syl6eq
    #
    @49
    @47
    c2
    clog
    @49
    @47
    c1
    c1
    caddc
    co
    c2
    @42
    c1
    c1
    caddc
    oveq1
    df-2
    syl6eqr
    fveq2d
    oveq12d
    emcl.2
    @1
    cr
    c1
    @0
    1re
    c2
    crp
    wcel
    @0
    cr
    wcel
    2rp
    c2
    relogcl
    ax-mp
    resubcli
    #
    elexi
    fvmpt
    ax-mp
    #
    syl6eq
    breq1d
    rspcva
    sylancr
    wtru
    @25
    cem
    @26
    cF
    cfv
    #
    cle
    wbr
    #
    vi
    cn
    wral
    @9
    1nn
    wtru
    @56
    vi
    cn
    @30
    @56
    @55
    cneg
    #
    cem
    cneg
    #
    cle
    wbr
    #
    @30
    @57
    cc0
    cem
    cmin
    co
    #
    @58
    cle
    @30
    @26
    vx
    cn
    vx
    cv
    #
    cF
    cfv
    #
    cneg
    #
    cmpt
    #
    cfv
    #
    @57
    @60
    cle
    @29
    @65
    @57
    wceq
    wtru
    vx
    @26
    @63
    @57
    cn
    @64
    @61
    @26
    wceq
    @62
    @55
    @61
    @26
    cF
    fveq2
    negeqd
    @64
    eqid
    #
    @55
    negex
    fvmpt
    adantl
    @30
    @60
    vk
    @64
    c1
    @26
    cn
    nnuz
    @31
    wtru
    @64
    @60
    cli
    wbr
    @29
    wtru
    cem
    cc0
    vk
    cF
    @64
    c1
    cvv
    cn
    nnuz
    @10
    @12
    wtru
    @12
    @11
    @13
    simpli
    a1i
    wtru
    0cnd
    @64
    cvv
    wcel
    wtru
    vx
    cn
    @63
    nnex
    mptex
    a1i
    wtru
    @16
    wa
    #
    @35
    @16
    @35
    cr
    wcel
    #
    wtru
    cn
    cr
    @15
    cF
    @19
    @20
    @21
    simpli
    #
    ffvelrni
    #
    adantl
    #
    recnd
    @67
    @15
    @64
    cfv
    #
    @35
    cneg
    #
    cc0
    @35
    cmin
    co
    @16
    @72
    @73
    wceq
    wtru
    vx
    @15
    @63
    @73
    cn
    @64
    @61
    @15
    wceq
    @62
    @35
    @61
    @15
    cF
    fveq2
    negeqd
    @66
    @35
    negex
    fvmpt
    adantl
    #
    @35
    df-neg
    syl6eq
    climsubc2
    adantr
    wtru
    @16
    @72
    cr
    wcel
    @29
    @67
    @72
    @73
    cr
    @74
    @67
    @35
    @71
    renegcld
    eqeltrd
    adantlr
    wtru
    @16
    @72
    @32
    @64
    cfv
    #
    cle
    wbr
    @29
    @67
    @73
    @34
    cneg
    #
    @72
    @75
    cle
    @67
    @36
    @73
    @76
    cle
    wbr
    @16
    @36
    wtru
    @16
    @36
    @33
    @37
    simpld
    #
    adantl
    @67
    @34
    @35
    @67
    @32
    cn
    wcel
    #
    @34
    cr
    wcel
    @16
    @78
    wtru
    @15
    peano2nn
    adantl
    #
    cn
    cr
    @32
    cF
    @69
    ffvelrni
    syl
    @71
    lenegd
    mpbid
    @74
    @67
    @78
    @75
    @76
    wceq
    @79
    vx
    @32
    @63
    @76
    cn
    @64
    @61
    @32
    wceq
    @62
    @34
    @61
    @32
    cF
    fveq2
    negeqd
    @66
    @34
    negex
    fvmpt
    syl
    3brtr4d
    adantlr
    climub
    eqbrtrrd
    cem
    df-neg
    syl6breqr
    @30
    @7
    @55
    cr
    wcel
    #
    @56
    @59
    wb
    @7
    @24
    trud
    #
    @29
    @80
    wtru
    cn
    cr
    @26
    cF
    @69
    ffvelrni
    adantl
    #
    cem
    @55
    leneg
    sylancr
    mpbird
    #
    ralrimiva
    @56
    @9
    vi
    c1
    cn
    @40
    @55
    c1
    cem
    cle
    @40
    @55
    c1
    cF
    cfv
    #
    c1
    @26
    c1
    cF
    fveq2
    @25
    @84
    c1
    wceq
    1nn
    vn
    c1
    @46
    @42
    clog
    cfv
    #
    cmin
    co
    #
    c1
    cn
    cF
    @49
    @86
    c1
    cc0
    cmin
    co
    c1
    @49
    @46
    c1
    @85
    cc0
    cmin
    @52
    @49
    @85
    c1
    clog
    cfv
    cc0
    @42
    c1
    clog
    fveq2
    log1
    syl6eq
    oveq12d
    1m0e1
    syl6eq
    emcl.1
    c1
    cr
    1re
    elexi
    fvmpt
    ax-mp
    #
    syl6eq
    breq2d
    rspcva
    sylancr
    @1
    c1
    cem
    @53
    1re
    elicc2i
    syl3anbrc
    wtru
    cF
    cn
    wfn
    #
    @55
    @3
    wcel
    #
    vi
    cn
    wral
    @4
    @19
    @88
    wtru
    @69
    cn
    cr
    cF
    ffn
    mp1i
    wtru
    @89
    vi
    cn
    @30
    @80
    @56
    @55
    c1
    cle
    wbr
    @89
    @82
    @83
    @30
    @55
    @84
    c1
    cle
    @30
    vk
    cF
    c1
    @26
    @30
    @26
    cn
    c1
    cuz
    cfv
    @31
    nnuz
    syl6eleq
    #
    @30
    @15
    c1
    @26
    cfz
    co
    wcel
    #
    wa
    #
    @16
    @68
    @91
    @16
    @30
    @15
    @26
    elfznn
    adantl
    #
    @70
    syl
    @30
    @15
    c1
    @26
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    wa
    #
    @16
    @36
    @95
    @16
    @30
    @15
    @94
    elfznn
    adantl
    #
    @77
    syl
    monoord2
    @87
    syl6breq
    cem
    c1
    @55
    @81
    1re
    elicc2i
    syl3anbrc
    ralrimiva
    vi
    cn
    @3
    cF
    ffnfv
    sylanbrc
    wtru
    cG
    cn
    wfn
    #
    @27
    @5
    wcel
    #
    vi
    cn
    wral
    @6
    @20
    @98
    wtru
    @22
    cn
    cr
    cG
    ffn
    mp1i
    wtru
    @99
    vi
    cn
    @30
    @27
    cr
    wcel
    #
    @1
    @27
    cle
    wbr
    @28
    @99
    @29
    @100
    wtru
    cn
    cr
    @26
    cG
    @22
    ffvelrni
    adantl
    @30
    @1
    @41
    @27
    cle
    @54
    @30
    vk
    cG
    c1
    @26
    @90
    @92
    @16
    @18
    @93
    @23
    syl
    @96
    @16
    @33
    @97
    @38
    syl
    monoord
    syl5eqbrr
    @39
    @1
    cem
    @27
    @53
    @81
    elicc2i
    syl3anbrc
    ralrimiva
    vi
    cn
    @5
    cG
    ffnfv
    sylanbrc
    3jca
    trud
end
