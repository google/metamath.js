include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "csn.mm"
include "cv.mm"
include "cphi.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "wceq.mm"
include "cc.mm"
include "crab.mm"
include "cun.mm"
include "czn.mm"
include "cbs.mm"
include "cmap.mm"
include "cfn.mm"
include "wss.mm"
include "snfi.mm"
include "chash.mm"
include "cmpt.mm"
include "cdgr.mm"
include "cle.mm"
include "wbr.mm"
include "cply.mm"
include "c0p.mm"
include "wne.mm"
include "wa.mm"
include "cxp.mm"
include "cof.mm"
include "cvv.mm"
include "cnex.mm"
include "a1i.mm"
include "ovexd.mm"
include "1cnd.mm"
include "eqidd.mm"
include "fconstmpt.mm"
include "offval2.mm"
include "cn0.mm"
include "ssid.mm"
include "phicl.mm"
include "nnnn0d.mm"
include "plypow.mm"
include "syl3anc.mm"
include "ax-1cn.mm"
include "plyconst.mm"
include "mp2an.mm"
include "plysubcl.mm"
include "sylancl.mm"
include "eqeltrrd.mm"
include "0cn.mm"
include "cneg.mm"
include "neg1ne0.mm"
include "0expd.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "df-neg.mm"
include "3eqtr4g.mm"
include "neeq1d.mm"
include "mpbiri.mm"
include "ne0p.mm"
include "sylancr.mm"
include "ccnv.mm"
include "cima.mm"
include "mptiniseg.mm"
include "eqcomi.mm"
include "fta1.mm"
include "syl2anc.mm"
include "simpld.mm"
include "unfi.mm"
include "znfi.mm"
include "mapfi.mm"
include "wf.mm"
include "wfn.mm"
include "wral.mm"
include "simpr.mm"
include "dchrf.mm"
include "ffn.mm"
include "syl.mm"
include "wo.mm"
include "wn.mm"
include "df-ne.mm"
include "fvex.mm"
include "elsn.mm"
include "xchbinxr.mm"
include "simpl.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "cmg.mm"
include "cur.mm"
include "cmhm.mm"
include "dchrmhm.mm"
include "simplr.mm"
include "sseldi.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "mgpbas.mm"
include "mhmmulg.mm"
include "cui.mm"
include "cress.mm"
include "c0g.mm"
include "cod.mm"
include "cdvds.mm"
include "cgrp.mm"
include "crg.mm"
include "ccrg.mm"
include "nnnn0.mm"
include "zncrng.mm"
include "crngring.mm"
include "unitgrp.mm"
include "znunithash.mm"
include "eqeltrd.mm"
include "wb.mm"
include "hashclb.mm"
include "sylibr.mm"
include "simprr.mm"
include "dchrn0.mm"
include "mpbid.mm"
include "unitgrpbas.mm"
include "oddvds2.mm"
include "breqtrd.mm"
include "cz.mm"
include "nnzd.mm"
include "oddvds.mm"
include "csubmnd.mm"
include "unitsubm.mm"
include "submmulg.mm"
include "ringidval.mm"
include "subm0.mm"
include "3eqtr4d.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "cnfldexp.mm"
include "cnfld1.mm"
include "mhm0.mm"
include "3eqtr3d.mm"
include "1m1e0.mm"
include "syl6eq.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "expr.mm"
include "syl5bir.mm"
include "orrd.mm"
include "elun.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "ex.mm"
include "elmapd.mm"
include "sylibrd.mm"
include "ssrdv.mm"
include "ssfi.mm"

theorem dchrfi
  let cD: class D
  let cG: class G
  let cN: class N
  let vf: setvar f
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  let vy: setvar y
  let vz: setvar z
  assume dchrabl.g: |- G = ( DChr ` N )
  assume dchrfi.b: |- D = ( Base ` G )


  assert |- ( N e. NN -> D e. Fin )

  proof
    cN
    cn
    wcel
    #
    cc0
    csn
    #
    vz
    cv
    #
    cN
    cphi
    cfv
    #
    cexp
    co
    #
    c1
    cmin
    co
    #
    cc0
    wceq
    #
    vz
    cc
    crab
    #
    cun
    #
    cN
    czn
    cfv
    #
    cbs
    cfv
    #
    cmap
    co
    #
    cfn
    wcel
    #
    cD
    @11
    wss
    cD
    cfn
    wcel
    @0
    @8
    cfn
    wcel
    #
    @10
    cfn
    wcel
    @12
    @0
    @1
    cfn
    wcel
    @7
    cfn
    wcel
    #
    @13
    cc0
    snfi
    @0
    @14
    @7
    chash
    cfv
    vz
    cc
    @5
    cmpt
    #
    cdgr
    cfv
    cle
    wbr
    #
    @0
    @15
    cc
    cply
    cfv
    #
    wcel
    @15
    c0p
    wne
    #
    @14
    @16
    wa
    @0
    vz
    cc
    @4
    cmpt
    #
    cc
    c1
    csn
    cxp
    #
    cmin
    cof
    co
    #
    @15
    @17
    @0
    vz
    cc
    @4
    c1
    cmin
    @19
    @20
    cvv
    cvv
    cc
    cc
    cvv
    wcel
    @0
    cnex
    a1i
    @0
    @2
    cc
    wcel
    wa
    #
    @2
    @3
    cexp
    ovexd
    @22
    1cnd
    @0
    @19
    eqidd
    @20
    vz
    cc
    c1
    cmpt
    wceq
    @0
    vz
    cc
    c1
    fconstmpt
    a1i
    offval2
    @0
    @19
    @17
    wcel
    #
    @20
    @17
    wcel
    #
    @21
    @17
    wcel
    @0
    cc
    cc
    wss
    #
    c1
    cc
    wcel
    #
    @3
    cn0
    wcel
    #
    @23
    @25
    @0
    cc
    ssid
    #
    a1i
    @0
    1cnd
    @0
    @3
    cN
    phicl
    #
    nnnn0d
    #
    vz
    cc
    @3
    plypow
    syl3anc
    @25
    @26
    @24
    @28
    ax-1cn
    c1
    cc
    plyconst
    mp2an
    cc
    @19
    @20
    plysubcl
    sylancl
    eqeltrrd
    @0
    cc0
    cc
    wcel
    #
    cc0
    @15
    cfv
    #
    cc0
    wne
    #
    @18
    0cn
    @0
    @33
    c1
    cneg
    #
    cc0
    wne
    neg1ne0
    @0
    @32
    @34
    cc0
    @0
    cc0
    @3
    cexp
    co
    #
    c1
    cmin
    co
    #
    cc0
    c1
    cmin
    co
    @32
    @34
    @0
    @35
    cc0
    c1
    cmin
    @0
    @3
    @29
    0expd
    oveq1d
    @31
    @32
    @36
    wceq
    0cn
    vz
    cc0
    @5
    @36
    cc
    @15
    @2
    cc0
    wceq
    @4
    @35
    c1
    cmin
    @2
    cc0
    @3
    cexp
    oveq1
    oveq1d
    @15
    eqid
    #
    @35
    c1
    cmin
    ovex
    fvmpt
    ax-mp
    c1
    df-neg
    3eqtr4g
    neeq1d
    mpbiri
    cc0
    @15
    ne0p
    sylancr
    @7
    cc
    @15
    @15
    ccnv
    @1
    cima
    #
    @7
    @31
    @38
    @7
    wceq
    0cn
    vz
    cc
    @5
    cc0
    @15
    cc
    @37
    mptiniseg
    ax-mp
    eqcomi
    fta1
    syl2anc
    simpld
    @1
    @7
    unfi
    sylancr
    #
    @10
    cN
    @9
    @9
    eqid
    #
    @10
    eqid
    #
    znfi
    #
    @8
    @10
    mapfi
    syl2anc
    @0
    vf
    cD
    @11
    @0
    vf
    cv
    #
    cD
    wcel
    #
    @10
    @8
    @43
    wf
    #
    @43
    @11
    wcel
    @0
    @44
    @45
    @0
    @44
    wa
    #
    @43
    @10
    wfn
    #
    vx
    cv
    #
    @43
    cfv
    #
    @8
    wcel
    #
    vx
    @10
    wral
    @45
    @46
    @10
    cc
    @43
    wf
    #
    @47
    @46
    @10
    cD
    cG
    cN
    @43
    @9
    dchrabl.g
    @40
    dchrfi.b
    @41
    @0
    @44
    simpr
    dchrf
    #
    @10
    cc
    @43
    ffn
    syl
    @46
    @50
    vx
    @10
    @46
    @48
    @10
    wcel
    #
    wa
    #
    @49
    @1
    wcel
    #
    @49
    @7
    wcel
    #
    wo
    @50
    @54
    @55
    @56
    @55
    wn
    @49
    cc0
    wne
    #
    @54
    @56
    @57
    @49
    cc0
    wceq
    @55
    @49
    cc0
    df-ne
    @49
    cc0
    @48
    @43
    fvex
    elsn
    xchbinxr
    @46
    @53
    @57
    @56
    @46
    @53
    @57
    wa
    #
    wa
    #
    @49
    cc
    wcel
    #
    @49
    @3
    cexp
    co
    #
    c1
    cmin
    co
    #
    cc0
    wceq
    #
    @56
    @46
    @51
    @53
    @60
    @58
    @52
    @53
    @57
    simpl
    @10
    cc
    @48
    @43
    ffvelrn
    syl2an
    #
    @59
    @62
    c1
    c1
    cmin
    co
    cc0
    @59
    @61
    c1
    c1
    cmin
    @59
    @3
    @49
    ccnfld
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    @9
    cur
    cfv
    #
    @43
    cfv
    #
    @61
    c1
    @59
    @3
    @48
    @9
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    @43
    cfv
    #
    @67
    @69
    @59
    @43
    @70
    @65
    cmhm
    co
    #
    wcel
    #
    @27
    @53
    @73
    @67
    wceq
    @59
    cD
    @74
    @43
    cD
    cG
    cN
    @9
    dchrabl.g
    @40
    dchrfi.b
    dchrmhm
    @0
    @44
    @58
    simplr
    #
    sseldi
    #
    @0
    @27
    @44
    @58
    @30
    ad2antrr
    #
    @46
    @53
    @57
    simprl
    #
    @10
    @71
    @66
    @43
    @70
    @65
    @3
    @48
    @10
    @9
    @70
    @70
    eqid
    #
    @41
    mgpbas
    @71
    eqid
    #
    @66
    eqid
    mhmmulg
    syl3anc
    @59
    @72
    @68
    @43
    @59
    @3
    @48
    @70
    @9
    cui
    cfv
    #
    cress
    co
    #
    cmg
    cfv
    #
    co
    #
    @83
    c0g
    cfv
    #
    @72
    @68
    @59
    @48
    @83
    cod
    cfv
    #
    cfv
    #
    @3
    cdvds
    wbr
    #
    @85
    @86
    wceq
    #
    @59
    @88
    @82
    chash
    cfv
    #
    @3
    cdvds
    @59
    @83
    cgrp
    wcel
    #
    @82
    cfn
    wcel
    #
    @48
    @82
    wcel
    #
    @88
    @91
    cdvds
    wbr
    @59
    @9
    crg
    wcel
    #
    @92
    @0
    @95
    @44
    @58
    @0
    @9
    ccrg
    wcel
    #
    @95
    @0
    cN
    cn0
    wcel
    @96
    cN
    nnnn0
    cN
    @9
    @40
    zncrng
    syl
    @9
    crngring
    syl
    ad2antrr
    #
    @9
    @82
    @83
    @82
    eqid
    #
    @83
    eqid
    #
    unitgrp
    syl
    #
    @0
    @93
    @44
    @58
    @0
    @91
    cn0
    wcel
    #
    @93
    @0
    @91
    @3
    cn0
    @82
    cN
    @9
    @40
    @98
    znunithash
    #
    @30
    eqeltrd
    @82
    cvv
    wcel
    @93
    @101
    wb
    @9
    cui
    fvex
    @82
    cvv
    hashclb
    ax-mp
    sylibr
    ad2antrr
    @59
    @57
    @94
    @46
    @53
    @57
    simprr
    @59
    @48
    @10
    cD
    @82
    cG
    cN
    @43
    @9
    dchrabl.g
    @40
    dchrfi.b
    @41
    @98
    @76
    @79
    dchrn0
    mpbid
    #
    @48
    @83
    @87
    @82
    @9
    @82
    @83
    @98
    @99
    unitgrpbas
    #
    @87
    eqid
    #
    oddvds2
    syl3anc
    @0
    @91
    @3
    wceq
    @44
    @58
    @102
    ad2antrr
    breqtrd
    @59
    @92
    @94
    @3
    cz
    wcel
    @89
    @90
    wb
    @100
    @103
    @59
    @3
    @0
    @3
    cn
    wcel
    @44
    @58
    @29
    ad2antrr
    nnzd
    @48
    @84
    @83
    @3
    @87
    @82
    @86
    @104
    @105
    @84
    eqid
    #
    @86
    eqid
    oddvds
    syl3anc
    mpbid
    @59
    @82
    @70
    csubmnd
    cfv
    wcel
    #
    @27
    @94
    @72
    @85
    wceq
    @59
    @95
    @107
    @97
    @9
    @82
    @70
    @98
    @80
    unitsubm
    syl
    #
    @78
    @103
    @82
    @71
    @84
    @70
    @83
    @3
    @48
    @81
    @99
    @106
    submmulg
    syl3anc
    @59
    @107
    @68
    @86
    wceq
    @108
    @82
    @83
    @70
    @68
    @99
    @9
    @68
    @70
    @80
    @68
    eqid
    ringidval
    #
    subm0
    syl
    3eqtr4d
    fveq2d
    eqtr3d
    @59
    @60
    @27
    @67
    @61
    wceq
    @64
    @78
    @49
    @3
    cnfldexp
    syl2anc
    @59
    @75
    @69
    c1
    wceq
    @77
    @70
    @65
    @43
    c1
    @68
    @109
    ccnfld
    c1
    @65
    @65
    eqid
    cnfld1
    ringidval
    mhm0
    syl
    3eqtr3d
    oveq1d
    1m1e0
    syl6eq
    @6
    @63
    vz
    @49
    cc
    @2
    @49
    wceq
    #
    @5
    @62
    cc0
    @110
    @4
    @61
    c1
    cmin
    @2
    @49
    @3
    cexp
    oveq1
    oveq1d
    eqeq1d
    elrab
    sylanbrc
    expr
    syl5bir
    orrd
    @49
    @1
    @7
    elun
    sylibr
    ralrimiva
    vx
    @10
    @8
    @43
    ffnfv
    sylanbrc
    ex
    @0
    @8
    @10
    @43
    cfn
    cfn
    @39
    @42
    elmapd
    sylibrd
    ssrdv
    @11
    cD
    ssfi
    syl2anc
end
